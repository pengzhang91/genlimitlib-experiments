import Stage3Model
import Mathlib.Topology.Algebra.Order.LiminfLimsup

open Filter
open scoped Topology

namespace Stage3Case019Proof

open GenLimit

private theorem prefixCount_inter_le_add_diff
    (G E K : Set ℕ) (hfinite : (E \ K).Finite) (n : ℕ) :
    PatientScope.prefixCount (G ∩ E) n ≤
      PatientScope.prefixCount (G ∩ K) n + hfinite.toFinset.card := by
  classical
  unfold PatientScope.prefixCount PatientScope.prefixFinset
  let left := (Finset.range n).filter fun x => x ∈ G ∩ E
  let main := (Finset.range n).filter fun x => x ∈ G ∩ K
  let extra := (Finset.range n).filter fun x => x ∈ E \ K
  have hsub : left ⊆ main ∪ extra := by
    intro x hx
    simp only [left, main, extra, Finset.mem_filter, Finset.mem_union,
      Set.mem_inter_iff, Set.mem_diff] at hx ⊢
    by_cases hxK : x ∈ K
    · exact Or.inl ⟨hx.1, hx.2.1, hxK⟩
    · exact Or.inr ⟨hx.1, hx.2.2, hxK⟩
  have hcard : left.card ≤ main.card + extra.card :=
    (Finset.card_le_card hsub).trans (Finset.card_union_le main extra)
  have hextra : extra.card ≤ hfinite.toFinset.card := by
    apply Finset.card_le_card
    intro x hx
    have hxmem : x ∈ extra := hx
    have hx' : x ∈ E \ K := by
      simpa only [extra, Finset.mem_filter] using (Finset.mem_filter.mp hxmem).2
    exact Set.Finite.mem_toFinset hfinite |>.2 hx'
  simpa [left, main, extra] using
    hcard.trans (Nat.add_le_add_left hextra _)

theorem relativeLowerDensity_inter_of_subset_finite
    {G E K : Set ℕ} (hK : K.Infinite) (hKE : K ⊆ E)
    (hfinite : (E \ K).Finite) :
    PatientScope.relativeLowerDensity (G ∩ E) E ≤
      PatientScope.relativeLowerDensity (G ∩ K) K := by
  let c : ℕ := hfinite.toFinset.card
  let f : ℕ → ℝ := fun n =>
    (PatientScope.prefixCount (G ∩ E) n : ℝ) /
      (PatientScope.prefixCount E n : ℝ)
  let g : ℕ → ℝ := fun n =>
    (PatientScope.prefixCount (G ∩ K) n : ℝ) /
      (PatientScope.prefixCount K n : ℝ)
  let e : ℕ → ℝ := fun n =>
    (c : ℝ) / (PatientScope.prefixCount K n : ℝ)
  have hKtend : Tendsto (PatientScope.prefixCount K) atTop atTop :=
    PatientScope.tendsto_prefixCount_atTop hK
  have he : Tendsto e atTop (𝓝 0) := by
    have hKreal :
        Tendsto (fun n => (PatientScope.prefixCount K n : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp hKtend
    exact hKreal.const_div_atTop (c : ℝ)
  have hcompare : ∀ᶠ n : ℕ in atTop, f n ≤ g n + e n := by
    have hpos : ∀ᶠ n : ℕ in atTop, 0 < PatientScope.prefixCount K n :=
      hKtend.eventually (eventually_gt_atTop 0)
    filter_upwards [hpos] with n hn
    have hnR : (0 : ℝ) < PatientScope.prefixCount K n := by exact_mod_cast hn
    have hden := PatientScope.prefixCount_mono hKE n
    have hnum := prefixCount_inter_le_add_diff G E K hfinite n
    have hdenR : (PatientScope.prefixCount K n : ℝ) ≤
        PatientScope.prefixCount E n := by exact_mod_cast hden
    have hnumR : (PatientScope.prefixCount (G ∩ E) n : ℝ) ≤
        PatientScope.prefixCount (G ∩ K) n + c := by
      exact_mod_cast hnum
    have hEnpos : (0 : ℝ) < PatientScope.prefixCount E n :=
      lt_of_lt_of_le hnR hdenR
    calc
      f n ≤ (PatientScope.prefixCount (G ∩ E) n : ℝ) /
          (PatientScope.prefixCount K n : ℝ) := by
        apply div_le_div_of_nonneg_left
        · positivity
        · exact hnR
        · exact hdenR
      _ ≤ ((PatientScope.prefixCount (G ∩ K) n : ℝ) + c) /
          (PatientScope.prefixCount K n : ℝ) :=
        div_le_div_of_nonneg_right hnumR hnR.le
      _ = g n + e n := by simp [f, g, e, c, add_div]
  have hf_nonneg : ∀ n, 0 ≤ f n := by intro n; positivity
  have hg_nonneg : ∀ n, 0 ≤ g n := by intro n; positivity
  have hg_le_one : ∀ n, g n ≤ 1 := by
    intro n
    by_cases hn : PatientScope.prefixCount K n = 0
    · simp [g, hn]
    · change
        (PatientScope.prefixCount (G ∩ K) n : ℝ) /
            (PatientScope.prefixCount K n : ℝ) ≤ 1
      rw [div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hn)]
      exact_mod_cast PatientScope.prefixCount_mono Set.inter_subset_right n
  have he_nonneg : ∀ n, 0 ≤ e n := by intro n; positivity
  have he_le : ∀ n, e n ≤ c := by
    intro n
    by_cases hn : PatientScope.prefixCount K n = 0
    · simp [e, hn]
    · have hn1 : (1 : ℝ) ≤ PatientScope.prefixCount K n := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
      calc
        e n ≤ (c : ℝ) / 1 := by
          apply div_le_div_of_nonneg_left
          · positivity
          · norm_num
          · exact hn1
        _ = c := by simp
  have hliminf : liminf f atTop ≤ liminf (g + e) atTop := by
    exact liminf_le_liminf hcompare
      (hu := isBoundedUnder_of ⟨0, hf_nonneg⟩)
      (hv := isCoboundedUnder_ge_of_le atTop (x := (1 + c : ℝ))
        (fun n => by change g n + e n ≤ 1 + c; linarith [hg_le_one n, he_le n]))
  have hadd : liminf (g + e) atTop ≤ liminf g atTop := by
    calc
      liminf (g + e) atTop ≤ limsup e atTop + liminf g atTop := by
        rw [add_comm]
        apply liminf_add_le
        · exact isBoundedUnder_of ⟨0, he_nonneg⟩
        · exact isBoundedUnder_of ⟨c, he_le⟩
        · exact isBoundedUnder_of ⟨0, hg_nonneg⟩
        · exact isCoboundedUnder_ge_of_le atTop hg_le_one
      _ = liminf g atTop := by rw [he.limsup_eq, zero_add]
  exact hliminf.trans hadd

end Stage3Case019Proof
