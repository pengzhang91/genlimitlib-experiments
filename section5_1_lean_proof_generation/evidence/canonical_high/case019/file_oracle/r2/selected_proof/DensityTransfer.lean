import Case019Helpers

open Set Filter
open scoped Topology

namespace Stage3Case019

noncomputable section

private theorem patient_prefixCount_le_finite {F : Set ℕ}
    (hF : F.Finite) (n : ℕ) :
    GenLimit.PatientScope.prefixCount F n ≤ hF.toFinset.card := by
  classical
  unfold GenLimit.PatientScope.prefixCount GenLimit.PatientScope.prefixFinset
  apply Finset.card_le_card
  intro x hx
  simp only [Finset.mem_filter, Finset.mem_range] at hx
  simpa using hx.2

private theorem patient_prefixCount_le_add_diff {A B : Set ℕ}
    (hF : (A \ B).Finite) (n : ℕ) :
    GenLimit.PatientScope.prefixCount A n ≤
      GenLimit.PatientScope.prefixCount B n + hF.toFinset.card := by
  classical
  let a := (Finset.range n).filter fun x => x ∈ A
  let b := (Finset.range n).filter fun x => x ∈ B
  let d := (Finset.range n).filter fun x => x ∈ A \ B
  have hsub : a ⊆ b ∪ d := by
    intro x hx
    simp only [a, b, d, Finset.mem_filter, Finset.mem_union] at hx ⊢
    by_cases hxb : x ∈ B
    · exact Or.inl ⟨hx.1, hxb⟩
    · exact Or.inr ⟨hx.1, hx.2, hxb⟩
  have hcard : a.card ≤ b.card + d.card :=
    (Finset.card_le_card hsub).trans (Finset.card_union_le b d)
  have hd : d.card ≤ hF.toFinset.card := by
    simpa [d, GenLimit.PatientScope.prefixCount,
      GenLimit.PatientScope.prefixFinset] using
      patient_prefixCount_le_finite hF n
  simpa [a, b, d, GenLimit.PatientScope.prefixCount,
    GenLimit.PatientScope.prefixFinset] using
    hcard.trans (Nat.add_le_add_left hd _)

/-- Removing finitely many points from both the measured set and its finite
extension target cannot decrease target-relative lower density. -/
theorem relativeLowerDensity_finiteExtension
    {A K E : Set ℕ} (hK : K.Infinite) (hKE : K ⊆ E)
    (hAE : A ⊆ E) (hfinite : (E \ K).Finite) :
    GenLimit.PatientScope.relativeLowerDensity A E ≤
      GenLimit.PatientScope.relativeLowerDensity (A ∩ K) K := by
  let f : ℕ → ℝ := fun n =>
    (GenLimit.PatientScope.prefixCount A n : ℝ) /
      GenLimit.PatientScope.prefixCount E n
  let g : ℕ → ℝ := fun n =>
    (GenLimit.PatientScope.prefixCount (A ∩ K) n : ℝ) /
      GenLimit.PatientScope.prefixCount K n
  let e : ℕ → ℝ := fun n =>
    (hfinite.toFinset.card : ℝ) /
      GenLimit.PatientScope.prefixCount E n
  have hE : E.Infinite := hK.mono hKE
  have he : Tendsto e atTop (nhds 0) := by
    exact tendsto_const_nhds.div_atTop
      (tendsto_natCast_atTop_atTop.comp
        (GenLimit.PatientScope.tendsto_prefixCount_atTop hE))
  have hfg : ∀ᶠ n : ℕ in atTop, f n ≤ g n + e n := by
    have hpos : ∀ᶠ n : ℕ in atTop,
        0 < GenLimit.PatientScope.prefixCount K n :=
      (GenLimit.PatientScope.tendsto_prefixCount_atTop hK).eventually
        (eventually_gt_atTop 0)
    filter_upwards [hpos] with n hn
    have hnK : (0 : ℝ) < GenLimit.PatientScope.prefixCount K n := by
      exact_mod_cast hn
    have hnE : (0 : ℝ) < GenLimit.PatientScope.prefixCount E n := by
      exact_mod_cast lt_of_lt_of_le hn
        (GenLimit.PatientScope.prefixCount_mono hKE n)
    let hdiff : (A \ (A ∩ K)).Finite := hfinite.subset (by
      intro x hx
      exact ⟨hAE hx.1, fun hxK => hx.2 ⟨hx.1, hxK⟩⟩)
    have hcount0 := patient_prefixCount_le_add_diff hdiff n
    have hcard : hdiff.toFinset.card ≤ hfinite.toFinset.card := by
      apply Finset.card_le_card
      intro x hx
      have hx' := hdiff.mem_toFinset.mp hx
      apply hfinite.mem_toFinset.mpr
      exact ⟨hAE hx'.1, fun hxK => hx'.2 ⟨hx'.1, hxK⟩⟩
    have hcount : GenLimit.PatientScope.prefixCount A n ≤
        GenLimit.PatientScope.prefixCount (A ∩ K) n +
          hfinite.toFinset.card :=
      hcount0.trans (Nat.add_le_add_left hcard _)
    have hcountR :
        (GenLimit.PatientScope.prefixCount A n : ℝ) ≤
          GenLimit.PatientScope.prefixCount (A ∩ K) n +
            hfinite.toFinset.card := by exact_mod_cast hcount
    have hden := GenLimit.PatientScope.prefixCount_mono hKE n
    dsimp [f, g, e]
    calc
      (GenLimit.PatientScope.prefixCount A n : ℝ) /
          GenLimit.PatientScope.prefixCount E n
          ≤ ((GenLimit.PatientScope.prefixCount (A ∩ K) n : ℕ) : ℝ) /
              GenLimit.PatientScope.prefixCount E n +
              (hfinite.toFinset.card : ℝ) /
                GenLimit.PatientScope.prefixCount E n := by
            rw [← add_div]
            exact div_le_div_of_nonneg_right hcountR hnE.le
      _ ≤ ((GenLimit.PatientScope.prefixCount (A ∩ K) n : ℕ) : ℝ) /
              GenLimit.PatientScope.prefixCount K n +
              (hfinite.toFinset.card : ℝ) /
                GenLimit.PatientScope.prefixCount E n := by
            gcongr
  have hboundg : ∀ n, g n ≤ 1 := by
    intro n
    by_cases hn : GenLimit.PatientScope.prefixCount K n = 0
    · simp [g, hn]
    · dsimp [g]
      rw [div_le_one (by positivity)]
      exact_mod_cast GenLimit.PatientScope.prefixCount_mono inter_subset_right n
  have hnonnegg : ∀ n, 0 ≤ g n := by
    intro n
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hcobg : Filter.IsCoboundedUnder (· ≥ ·) atTop g :=
    isCoboundedUnder_ge_of_le atTop hboundg
  have hbdg : Filter.IsBoundedUnder (· ≥ ·) atTop g :=
    ⟨0, show ∀ᶠ n : ℕ in atTop, g n ≥ 0 from
      Eventually.of_forall hnonnegg⟩
  have hnonnegf : ∀ n, 0 ≤ f n := by
    intro n
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hbdf : Filter.IsBoundedUnder (· ≥ ·) atTop f :=
    ⟨0, show ∀ᶠ n : ℕ in atTop, f n ≥ 0 from
      Eventually.of_forall hnonnegf⟩
  rw [GenLimit.PatientScope.relativeLowerDensity,
    GenLimit.PatientScope.relativeLowerDensity]
  change liminf f atTop ≤ liminf g atTop
  apply (le_liminf_iff' hcobg hbdg).2
  intro y hy
  obtain ⟨z, hyz, hz⟩ := exists_between hy
  have hfz : ∀ᶠ n in atTop, z < f n :=
    eventually_lt_of_lt_liminf hz hbdf
  have hevent : ∀ᶠ n in atTop, e n < z - y := by
    have hpos : 0 < z - y := sub_pos.mpr hyz
    exact (tendsto_order.1 he).2 _ hpos
  filter_upwards [hfg, hfz, hevent] with n hfg' hfz' he'
  linarith

end

end Stage3Case019
