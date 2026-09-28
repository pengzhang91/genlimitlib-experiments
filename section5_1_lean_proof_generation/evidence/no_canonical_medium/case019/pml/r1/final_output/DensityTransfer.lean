import output.CountablePartial

open Set Filter
open scoped Topology

namespace Stage3Case019

open GenLimit
open GenLimit.PatientScope

private theorem prefixCount_le_add_finite
    {A B : Set ℕ} (hfinite : (A \ B).Finite) (n : ℕ) :
    prefixCount A n ≤ prefixCount B n + hfinite.toFinset.card := by
  classical
  unfold prefixCount
  let a := (Finset.range n).filter fun x => x ∈ A
  let b := (Finset.range n).filter fun x => x ∈ B
  let d := (Finset.range n).filter fun x => x ∈ A \ B
  have hsub : a ⊆ b ∪ d := by
    intro x hx
    simp only [a, b, d, Finset.mem_filter, Finset.mem_union] at hx ⊢
    by_cases hxB : x ∈ B
    · exact Or.inl ⟨hx.1, hxB⟩
    · exact Or.inr ⟨hx.1, hx.2, hxB⟩
  have hd : d.card ≤ hfinite.toFinset.card := by
    apply Finset.card_le_card
    intro x hx
    simp only [d, Finset.mem_filter] at hx
    exact Set.Finite.mem_toFinset hfinite |>.2 hx.2
  exact (Finset.card_le_card hsub).trans
    ((Finset.card_union_le b d).trans (Nat.add_le_add_left hd _))

 theorem relativeLowerDensity_finite_extension
    {K E A : Set ℕ} (hK : K.Infinite) (hsub : K ⊆ E)
    (hfinite : (E \ K).Finite) :
    relativeLowerDensity (A ∩ E) E ≤ relativeLowerDensity (A ∩ K) K := by
  let N : ℕ → ℕ := prefixCount K
  let fE : ℕ → ℝ := fun n =>
    (prefixCount (A ∩ E) n : ℝ) / (prefixCount E n : ℝ)
  let fK : ℕ → ℝ := fun n =>
    (prefixCount (A ∩ K) n : ℝ) / (N n : ℝ)
  let hdiff : ((A ∩ E) \ (A ∩ K)).Finite := hfinite.subset (by
    intro x hx
    exact ⟨hx.1.2, fun hxK => hx.2 ⟨hx.1.1, hxK⟩⟩)
  let c : ℕ := hdiff.toFinset.card
  let err : ℕ → ℝ := fun n => (c : ℝ) / (N n : ℝ)
  have hN := tendsto_prefixCount_atTop hK
  have hNR : Tendsto (fun n => (N n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hN
  have herr : Tendsto err atTop (𝓝 0) := by
    exact tendsto_const_nhds.div_atTop hNR
  have hpositive : ∀ᶠ n in atTop, 0 < N n :=
    hN.eventually (eventually_gt_atTop 0)
  have hcount (n : ℕ) :
      prefixCount (A ∩ E) n ≤ prefixCount (A ∩ K) n + c := by
    simpa [c] using
      prefixCount_le_add_finite (A := A ∩ E) (B := A ∩ K) hdiff n
  have hden (n : ℕ) : N n ≤ prefixCount E n :=
    prefixCount_mono hsub n
  have hcompare : ∀ᶠ n in atTop, fE n ≤ err n + fK n := by
    filter_upwards [hpositive] with n hn
    have hnR : (0 : ℝ) < N n := by exact_mod_cast hn
    have hdenR : (N n : ℝ) ≤ prefixCount E n := by exact_mod_cast hden n
    have hnumR : (prefixCount (A ∩ E) n : ℝ) ≤
        prefixCount (A ∩ K) n + c := by exact_mod_cast hcount n
    dsimp [fE, fK, err, N, c]
    calc
      (prefixCount (A ∩ E) n : ℝ) / prefixCount E n
          ≤ (prefixCount (A ∩ E) n : ℝ) / N n := by
            exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hnR hdenR
      _ ≤ ((prefixCount (A ∩ K) n : ℝ) + c) / N n := by
            exact div_le_div_of_nonneg_right hnumR (le_of_lt hnR)
      _ = (c : ℝ) / N n + (prefixCount (A ∩ K) n : ℝ) / N n := by ring
  have hfE_nonneg : ∀ n, 0 ≤ fE n := by
    intro n
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hfK_nonneg : ∀ n, 0 ≤ fK n := by
    intro n
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hfK_le : ∀ n, fK n ≤ 1 := by
    intro n
    by_cases hn : N n = 0
    · simp [fK, hn]
    · have hnR : (0 : ℝ) < N n := by exact_mod_cast Nat.pos_of_ne_zero hn
      rw [div_le_one hnR]
      exact_mod_cast prefixCount_mono (Set.inter_subset_right) n
  have hfirst : liminf fE atTop ≤ liminf (err + fK) atTop :=
    liminf_le_liminf hcompare
      (isBoundedUnder_of_eventually_ge (Eventually.of_forall hfE_nonneg))
      (isCoboundedUnder_ge_of_le atTop (x := (c : ℝ) + 1) (fun n => by
        have herr_le : err n ≤ c := by
          dsimp [err]
          by_cases hn : N n = 0
          · simp [hn]
          · have hnR : (1 : ℝ) ≤ N n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
            exact (div_le_iff₀ (by positivity : (0 : ℝ) < N n)).2 (by
              have hc : (0 : ℝ) ≤ (c : ℝ) := Nat.cast_nonneg c
              nlinarith)
        change err n + fK n ≤ (c : ℝ) + 1
        exact add_le_add herr_le (hfK_le n)))
  have hadd : liminf (err + fK) atTop ≤ limsup err atTop + liminf fK atTop :=
    liminf_add_le herr.isBoundedUnder_ge herr.isBoundedUnder_le
      (isBoundedUnder_of_eventually_ge (Eventually.of_forall hfK_nonneg))
      (isCoboundedUnder_ge_of_le atTop hfK_le)
  have hfinal : liminf fE atTop ≤ liminf fK atTop := by
    calc
      liminf fE atTop ≤ liminf (err + fK) atTop := hfirst
      _ ≤ limsup err atTop + liminf fK atTop := hadd
      _ = liminf fK atTop := by rw [herr.limsup_eq]; simp
  simpa [relativeLowerDensity, fE, fK, N] using hfinal

end Stage3Case019
