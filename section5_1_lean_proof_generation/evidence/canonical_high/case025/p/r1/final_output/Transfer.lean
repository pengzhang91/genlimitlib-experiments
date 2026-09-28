import Stage3Model
import Mathlib

open Set Filter
open scoped Topology

namespace Stage3Case025

noncomputable section

private def finiteAdditions (family : ℕ → Language) : ℕ → Language :=
  fun n =>
    let code := (Denumerable.eqv (ℕ × Finset ℕ)).symm n
    family code.1 ∪ (code.2 : Set ℕ)

private theorem finiteAdditions_infinite
    (family : ℕ → Language) (hfamily : ∀ i, (family i).Infinite) :
    ∀ n, (finiteAdditions family n).Infinite := by
  intro n
  exact (hfamily ((Denumerable.eqv (ℕ × Finset ℕ)).symm n).1).mono (by
    intro x hx
    exact Or.inl hx)

private theorem finiteAdditions_contains
    (family : ℕ → Language) (i : ℕ) (F : Set ℕ) (hF : F.Finite) :
    ∃ j, finiteAdditions family j = family i ∪ F := by
  let code : ℕ × Finset ℕ := (i, hF.toFinset)
  refine ⟨(Denumerable.eqv (ℕ × Finset ℕ)) code, ?_⟩
  change family ((Denumerable.eqv (ℕ × Finset ℕ)).symm ((Denumerable.eqv (ℕ × Finset ℕ)) code)).1 ∪
      (((Denumerable.eqv (ℕ × Finset ℕ)).symm ((Denumerable.eqv (ℕ × Finset ℕ)) code)).2 : Set ℕ) = _
  rw [Equiv.symm_apply_apply]
  simp [code, hF.coe_toFinset]

private theorem range_diff_finite
    {input : Stream} {K : Language}
    (hbad : GenLimit.Generic.FinitelyManyViolations input (fun x => x ∈ K)) :
    (Set.range input \ K).Finite := by
  apply Set.Finite.subset (hbad.image input)
  intro x hx
  rcases hx.1 with ⟨t, rfl⟩
  exact ⟨t, ⟨hx.2, rfl⟩⟩

private theorem tail_injective_of_novel
    {input output : Stream} {R : Language} {T : ℕ}
    (h : ∀ t, T ≤ t →
      output t ∈ R ∧ output t ∉ GenLimit.sample input (t + 1) ∧
        ∀ s, s < t → output s ≠ output t) :
    Set.InjOn output (Set.Ici T) := by
  intro a ha b hb hab
  rcases lt_trichotomy a b with hablt | rfl | hbag
  · exact False.elim ((h b hb).2.2 a hablt hab)
  · rfl
  · exact False.elim ((h a ha).2.2 b hbag (Eq.symm hab))

private theorem novel_of_finite_difference
    {input output : Stream} {K R : Language}
    (hfinite : (R \ K).Finite)
    (hnovel : GenLimit.NovelGeneratesInLimit input output R) :
    GenLimit.NovelGeneratesInLimit input output K := by
  rcases hnovel with ⟨T, hT⟩
  have hinj : Set.InjOn output (Set.Ici T) := tail_injective_of_novel hT
  let badTimes : Set ℕ := Set.Ici T ∩ output ⁻¹' (R \ K)
  have hbadTimes : badTimes.Finite := by
    apply Set.Finite.of_finite_image (f := output)
    · exact hfinite.subset (by
        intro x hx
        rcases hx with ⟨t, ht, rfl⟩
        exact ht.2)
    · intro a ha b hb hab
      exact hinj ha.1 hb.1 hab
  obtain ⟨B, hB⟩ := hbadTimes.exists_le
  refine ⟨max T (B + 1), ?_⟩
  intro t ht
  have hTt : T ≤ t := le_trans (le_max_left _ _) ht
  have hbase := hT t hTt
  refine ⟨?_, hbase.2.1, hbase.2.2⟩
  by_contra hnotK
  have htbad : t ∈ badTimes := ⟨hTt, hbase.1, hnotK⟩
  have htB := hB t htbad
  have hBt : B + 1 ≤ t := le_trans (le_max_right _ _) ht
  omega

end

end Stage3Case025

namespace Stage3Case025

noncomputable section

private theorem prefixCount_eq_sum_indicator (S : Set ℕ) (n : ℕ) :
    GenLimit.PatientScope.prefixCount S n =
      ∑ k ∈ Finset.range n, S.indicator (fun _ => 1) k := by
  classical
  simp [GenLimit.PatientScope.prefixCount, GenLimit.PatientScope.prefixFinset, Set.indicator]

private theorem prefixCount_tendsto_atTop {S : Set ℕ} (hS : S.Infinite) :
    Tendsto (GenLimit.PatientScope.prefixCount S) atTop atTop := by
  rw [Set.infinite_iff_tendsto_sum_indicator_atTop (R := ℕ) (r := 1) (by omega)] at hS
  convert hS using 1
  funext n
  exact prefixCount_eq_sum_indicator S n

private theorem prefixFinset_union (S T : Set ℕ) (n : ℕ) :
    GenLimit.PatientScope.prefixFinset (S ∪ T) n =
      GenLimit.PatientScope.prefixFinset S n ∪ GenLimit.PatientScope.prefixFinset T n := by
  classical
  ext x
  simp [GenLimit.PatientScope.prefixFinset]
  tauto

private theorem prefixCount_union_of_disjoint {S T : Set ℕ}
    (h : Disjoint S T) (n : ℕ) :
    GenLimit.PatientScope.prefixCount (S ∪ T) n =
      GenLimit.PatientScope.prefixCount S n + GenLimit.PatientScope.prefixCount T n := by
  classical
  rw [GenLimit.PatientScope.prefixCount, GenLimit.PatientScope.prefixCount,
    GenLimit.PatientScope.prefixCount, prefixFinset_union]
  rw [Finset.card_union_of_disjoint]
  exact Finset.disjoint_left.2 (by
    intro x hxS hxT
    exact Set.disjoint_left.1 h
      (Finset.mem_filter.1 hxS).2 (Finset.mem_filter.1 hxT).2)

private theorem prefixCount_mono {S T : Set ℕ} (h : S ⊆ T) (n : ℕ) :
    GenLimit.PatientScope.prefixCount S n ≤ GenLimit.PatientScope.prefixCount T n := by
  classical
  exact Finset.card_le_card (by
    intro x hx
    simp only [GenLimit.PatientScope.prefixFinset, Finset.mem_filter,
      Finset.mem_range] at hx ⊢
    exact ⟨hx.1, h hx.2⟩)

private theorem prefixCount_le_natCard {S : Set ℕ} (hS : S.Finite) (n : ℕ) :
    GenLimit.PatientScope.prefixCount S n ≤ Nat.card S := by
  classical
  rw [Nat.card_eq_card_finite_toFinset hS]
  exact Finset.card_le_card (by
    intro x hx
    exact hS.mem_toFinset.2 (Finset.mem_filter.1 hx).2)

private theorem finite_extension_density
    {A K F : Set ℕ} (hK : K.Infinite) (hF : F.Finite) (hdisj : Disjoint K F)
    (hdensity : (1 / 2 : ℝ) ≤
      GenLimit.PatientScope.relativeLowerDensity (A ∩ (K ∪ F)) (K ∪ F)) :
    (1 / 2 : ℝ) ≤ GenLimit.PatientScope.relativeLowerDensity (A ∩ K) K := by
  let kc : ℕ → ℕ := GenLimit.PatientScope.prefixCount K
  let ac : ℕ → ℕ := GenLimit.PatientScope.prefixCount (A ∩ K)
  let fc : ℕ → ℕ := GenLimit.PatientScope.prefixCount F
  let bc : ℕ → ℕ := GenLimit.PatientScope.prefixCount (A ∩ F)
  let C : ℕ := Nat.card F
  let u : ℕ → ℝ := fun n => ((ac n + bc n : ℕ) : ℝ) / ((kc n + fc n : ℕ) : ℝ)
  let v : ℕ → ℝ := fun n => (ac n : ℝ) / (kc n : ℝ)
  let err : ℕ → ℝ := fun n => (C : ℝ) / (kc n : ℝ)
  have htarget : ∀ n,
      GenLimit.PatientScope.prefixCount (K ∪ F) n = kc n + fc n := by
    intro n
    exact prefixCount_union_of_disjoint hdisj n
  have hnum : ∀ n,
      GenLimit.PatientScope.prefixCount (A ∩ (K ∪ F)) n = ac n + bc n := by
    intro n
    have heq : A ∩ (K ∪ F) = (A ∩ K) ∪ (A ∩ F) := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_union]
      tauto
    rw [heq]
    apply prefixCount_union_of_disjoint
    exact Set.disjoint_left.2 (by
      intro x hxK hxF
      exact Set.disjoint_left.1 hdisj hxK.2 hxF.2)
  have hu_def : GenLimit.PatientScope.relativeLowerDensity
      (A ∩ (K ∪ F)) (K ∪ F) = liminf u atTop := by
    unfold GenLimit.PatientScope.relativeLowerDensity
    congr 1
    funext n
    rw [hnum n, htarget n]
  have hv_def : GenLimit.PatientScope.relativeLowerDensity (A ∩ K) K = liminf v atTop := by
    rfl
  rw [hu_def] at hdensity
  rw [hv_def]
  have hkc : Tendsto kc atTop atTop := prefixCount_tendsto_atTop hK
  have hkcast : Tendsto (fun n => (kc n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hkc
  have herr : Tendsto err atTop (nhds 0) := by
    exact Filter.Tendsto.div_atTop tendsto_const_nhds hkcast
  have hcompare : ∀ᶠ n in atTop, u n ≤ v n + err n := by
    have hkpos : ∀ᶠ n in atTop, 0 < kc n := by
      filter_upwards [(tendsto_atTop.1 hkc 1)] with n hn
      omega
    filter_upwards [hkpos] with n hn
    have hac_le : ac n ≤ kc n := prefixCount_mono (by intro x hx; exact hx.2) n
    have hbc_le : bc n ≤ C :=
      le_trans (prefixCount_mono (by intro x hx; exact hx.2) n)
        (prefixCount_le_natCard hF n)
    have hkr : (0 : ℝ) < kc n := by exact_mod_cast hn
    have hden : (0 : ℝ) < (kc n + fc n : ℕ) := by
      exact_mod_cast (Nat.add_pos_left hn (fc n))
    dsimp [u, v, err]
    have hnum_le : ((ac n + bc n : ℕ) : ℝ) ≤ ((ac n + C : ℕ) : ℝ) := by
      exact_mod_cast Nat.add_le_add_left hbc_le (ac n)
    calc
      ((ac n + bc n : ℕ) : ℝ) / ((kc n + fc n : ℕ) : ℝ)
          ≤ ((ac n + C : ℕ) : ℝ) / ((kc n + fc n : ℕ) : ℝ) :=
            (div_le_div_iff_of_pos_right hden).2 hnum_le
      _ ≤ ((ac n + C : ℕ) : ℝ) / (kc n : ℝ) := by
        apply div_le_div_of_nonneg_left (by positivity) hkr
        exact_mod_cast Nat.le_add_right (kc n) (fc n)
      _ = (ac n : ℝ) / (kc n : ℝ) + (C : ℝ) / (kc n : ℝ) := by
        push_cast
        ring
  have hv_nonneg : ∀ n, (0 : ℝ) ≤ v n := by
    intro n
    dsimp [v]
    positivity
  have hv_le_one : ∀ n, v n ≤ (1 : ℝ) := by
    intro n
    by_cases hk0 : kc n = 0
    · simp [v, hk0]
    · have hkpos : (0 : ℝ) < kc n := by exact_mod_cast Nat.pos_of_ne_zero hk0
      dsimp [v]
      rw [div_le_one hkpos]
      exact_mod_cast prefixCount_mono (by intro x hx; exact hx.2) n
  have hu_nonneg : ∀ n, (0 : ℝ) ≤ u n := by
    intro n
    dsimp [u]
    positivity
  have hv_below : IsBoundedUnder (fun x y : ℝ => x ≥ y) atTop v :=
    isBoundedUnder_of_eventually_ge (Eventually.of_forall hv_nonneg)
  have hv_cobounded : IsCoboundedUnder (fun x y : ℝ => x ≥ y) atTop v :=
    isCoboundedUnder_ge_of_le atTop hv_le_one
  have hu_below : IsBoundedUnder (fun x y : ℝ => x ≥ y) atTop u :=
    isBoundedUnder_of_eventually_ge (Eventually.of_forall hu_nonneg)
  rw [le_liminf_iff' hv_cobounded hv_below]
  intro y hy
  let z : ℝ := (y + (1 / 2 : ℝ)) / 2
  have hyz : y < z := by dsimp [z]; linarith
  have hzh : z < (1 / 2 : ℝ) := by dsimp [z]; linarith
  have hzlim : z < liminf u atTop := lt_of_lt_of_le hzh hdensity
  have hu_event : ∀ᶠ n in atTop, z < u n := eventually_lt_of_lt_liminf hzlim hu_below
  have herr_event : ∀ᶠ n in atTop, err n < z - y := by
    apply herr.eventually_lt_const
    linarith
  filter_upwards [hcompare, hu_event, herr_event] with n huv hzu he
  linarith

end

end Stage3Case025

namespace Stage3Case025

noncomputable section

/-- The finite-addition/no-omission transfer from the canonical proof. -/
theorem checked_finite_noise_transfer : FiniteNoiseTransferPrinciple := by
  intro hpositive family hfamily
  obtain ⟨gen, hgen⟩ := hpositive (finiteAdditions family)
    (finiteAdditions_infinite family hfamily)
  refine ⟨gen, ?_⟩
  intro i input hpresentation
  let K : Language := family i
  let R : Language := Set.range input
  let F : Set ℕ := R \ K
  have hKR : K ⊆ R := hpresentation.1
  have hF : F.Finite := range_diff_finite hpresentation.2
  have hR : K ∪ F = R := by
    ext x
    constructor
    · intro hx
      rcases hx with hx | hx
      · exact hKR hx
      · exact hx.1
    · intro hx
      by_cases hxK : x ∈ K
      · exact Or.inl hxK
      · exact Or.inr ⟨hx, hxK⟩
  obtain ⟨j, hj⟩ := finiteAdditions_contains family i F hF
  have hjR : finiteAdditions family j = R := by
    rw [hj]
    exact hR
  have hpresents : GenLimit.Presents input (finiteAdditions family j) := by
    unfold GenLimit.Presents
    exact hjR.symm
  obtain ⟨output, hfollows, hnovel, hdensity⟩ := hgen j input hpresents
  refine ⟨output, hfollows, ?_, ?_⟩
  · apply novel_of_finite_difference hF
    rwa [hjR] at hnovel
  · have hdisj : Disjoint K F := Set.disjoint_left.2 (by
      intro x hxK hxF
      exact hxF.2 hxK)
    apply finite_extension_density (hK := hfamily i) hF hdisj
    have hKF : K ∪ F = finiteAdditions family j := by
      rw [hj]
    rw [hKF]
    exact hdensity

end

end Stage3Case025
