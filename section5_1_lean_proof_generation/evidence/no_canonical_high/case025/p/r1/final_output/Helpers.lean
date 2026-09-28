import Stage3Model
import Mathlib.Logic.Equiv.Finset
import Mathlib.Topology.Algebra.Order.LiminfLimsup

open Set Filter
open scoped Topology

namespace Stage3Case025

noncomputable def decodedFinset (n : ℕ) : Finset ℕ :=
  (Encodable.decode n).getD ∅

lemma decodedFinset_encode (s : Finset ℕ) : decodedFinset (Encodable.encode s) = s := by
  simp [decodedFinset, Encodable.encodek]

noncomputable def finiteExtensionFamily (family : ℕ → Language) : ℕ → Language :=
  fun n => family (Nat.unpair n).1 ∪ (decodedFinset (Nat.unpair n).2 : Set ℕ)

lemma finiteExtensionFamily_infinite
    (family : ℕ → Language) (hfamily : ∀ i, (family i).Infinite) :
    ∀ n, (finiteExtensionFamily family n).Infinite := by
  intro n
  exact (hfamily (Nat.unpair n).1).mono (by
    intro x hx
    exact Or.inl hx)

lemma finiteExtensionFamily_pair (family : ℕ → Language) (i : ℕ) (s : Finset ℕ) :
    finiteExtensionFamily family (Nat.pair i (Encodable.encode s)) = family i ∪ (s : Set ℕ) := by
  simp [finiteExtensionFamily, decodedFinset_encode, Nat.unpair_pair]

lemma finite_violation_values
    {input : Stream} {K : Language}
    (hbad : GenLimit.Generic.FinitelyManyViolations input (fun x => x ∈ K)) :
    (input '' GenLimit.Generic.ViolationIndices input (fun x => x ∈ K)).Finite := by
  exact hbad.image input

lemma range_eq_target_union_violation_values
    {input : Stream} {K : Language}
    (hcover : K ⊆ Set.range input) :
    Set.range input = K ∪ (input '' GenLimit.Generic.ViolationIndices input (fun x => x ∈ K)) := by
  ext x
  constructor
  · rintro ⟨t, rfl⟩
    by_cases hx : input t ∈ K
    · exact Or.inl hx
    · exact Or.inr ⟨t, hx, rfl⟩
  · intro hx
    rcases hx with hx | ⟨t, -, rfl⟩
    · exact hcover hx
    · exact ⟨t, rfl⟩

lemma generatorFirst_avoids_seen
    {input output : Stream} {t : ℕ}
    (hfresh : output t ∉ GenLimit.sample input (t + 1)) :
    output t ∈ GenLimit.GeneratorFirst input output := by
  refine ⟨t, rfl, ?_⟩
  intro s hs heq
  apply hfresh
  simp [GenLimit.sample]
  exact ⟨s, by omega, heq⟩

end Stage3Case025

namespace Stage3Case025

lemma novelGeneratesInLimit_remove_finite
    {input output : Stream} {K B : Language}
    (hB : B.Finite)
    (hnovel : GenLimit.NovelGeneratesInLimit input output (K ∪ B)) :
    GenLimit.NovelGeneratesInLimit input output K := by
  rcases hnovel with ⟨T, hT⟩
  let badTimes : Set ℕ := {t | T ≤ t ∧ output t ∈ B}
  have hmap : MapsTo output badTimes B := by
    intro t ht
    exact ht.2
  have hinj : InjOn output badTimes := by
    intro s hs t ht heq
    by_contra hst
    rcases lt_or_gt_of_ne hst with hlt | hgt
    · exact (hT t ht.1).2.2 s hlt heq
    · exact (hT s hs.1).2.2 t hgt heq.symm
  have hbadFinite : badTimes.Finite := Set.Finite.of_injOn hmap hinj hB
  rcases bddAbove_def.mp hbadFinite.bddAbove with ⟨M, hM⟩
  refine ⟨max T (M + 1), ?_⟩
  intro t ht
  have htT : T ≤ t := le_trans (le_max_left _ _) ht
  have hall := hT t htT
  refine ⟨?_, hall.2.1, hall.2.2⟩
  rcases hall.1 with hK | hBout
  · exact hK
  · exfalso
    have htbad : t ∈ badTimes := ⟨htT, hBout⟩
    have htM := hM t htbad
    have hMt : M + 1 ≤ t := le_trans (le_max_right _ _) ht
    omega

end Stage3Case025

namespace Stage3Case025

open GenLimit.PatientScope

lemma prefixCount_tendsto_atTop {K : Language} (hK : K.Infinite) :
    Tendsto (fun n => prefixCount K n) atTop atTop := by
  have ht := (Set.infinite_iff_tendsto_sum_indicator_atTop
    (R := ℕ) (r := 1) (by omega)).mp hK
  convert ht using 1
  funext n
  classical
  simp [prefixCount, prefixFinset, Set.indicator]

lemma prefixCount_mono_set {A C : Language} (hAC : A ⊆ C) (n : ℕ) :
    prefixCount A n ≤ prefixCount C n := by
  classical
  change (prefixFinset A n).card ≤ (prefixFinset C n).card
  apply Finset.card_le_card
  intro x hx
  simp only [prefixFinset, Finset.mem_filter] at hx ⊢
  exact ⟨hx.1, hAC hx.2⟩

lemma prefixCount_union_finite_le {A B : Language} (hB : B.Finite) (n : ℕ) :
    prefixCount (A ∪ B) n ≤ prefixCount A n + Nat.card B := by
  classical
  calc
    prefixCount (A ∪ B) n ≤
        (prefixFinset A n ∪ hB.toFinset).card := by
          apply Finset.card_le_card
          intro x hx
          simp only [prefixFinset, Finset.mem_filter] at hx
          apply Finset.mem_union.mpr
          rcases hx.2 with hxA | hxB
          · exact Or.inl (by
              simp only [prefixFinset, Finset.mem_filter]
              exact ⟨hx.1, hxA⟩)
          · exact Or.inr (hB.mem_toFinset.mpr hxB)
    _ ≤ (prefixFinset A n).card + hB.toFinset.card := Finset.card_union_le _ _
    _ = prefixCount A n + Nat.card B := by
      rw [Nat.card_eq_card_finite_toFinset hB]
      rfl

lemma prefixCount_inter_union_finite_le
    {D A B : Language} (hB : B.Finite) (n : ℕ) :
    prefixCount (D ∩ (A ∪ B)) n ≤ prefixCount (D ∩ A) n + Nat.card B := by
  calc
    prefixCount (D ∩ (A ∪ B)) n ≤ prefixCount ((D ∩ A) ∪ B) n := by
      apply prefixCount_mono_set
      intro x hx
      rcases hx with ⟨hxD, hxA | hxB⟩
      · exact Or.inl ⟨hxD, hxA⟩
      · exact Or.inr hxB
    _ ≤ prefixCount (D ∩ A) n + Nat.card B := prefixCount_union_finite_le hB n

end Stage3Case025

namespace Stage3Case025

open GenLimit.PatientScope

noncomputable def relativeRatio (A K : Language) (n : ℕ) : ℝ :=
  (prefixCount A n : ℝ) / (prefixCount K n : ℝ)

lemma relativeRatio_nonneg (A K : Language) (n : ℕ) :
    0 ≤ relativeRatio A K n := by
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

lemma relativeRatio_finite_extension_le
    {D K B : Language} (hB : B.Finite) {n : ℕ}
    (hn : 0 < prefixCount K n) :
    relativeRatio (D ∩ (K ∪ B)) (K ∪ B) n ≤
      relativeRatio (D ∩ K) K n + (Nat.card B : ℝ) / prefixCount K n := by
  have hnum := prefixCount_inter_union_finite_le (D := D) (A := K) hB n
  have hden := prefixCount_mono_set (A := K) (C := K ∪ B) (by
    intro x hx
    exact Or.inl hx) n
  have hc : (0 : ℝ) < prefixCount (K ∪ B) n := by
    exact_mod_cast (lt_of_lt_of_le hn hden)
  have hd : (0 : ℝ) < prefixCount K n := by
    exact_mod_cast hn
  unfold relativeRatio
  calc
    (prefixCount (D ∩ (K ∪ B)) n : ℝ) / prefixCount (K ∪ B) n ≤
        (prefixCount (D ∩ (K ∪ B)) n : ℝ) / prefixCount K n := by
          gcongr
    _ ≤ ((prefixCount (D ∩ K) n + Nat.card B : ℕ) : ℝ) / prefixCount K n := by
          gcongr
    _ = (prefixCount (D ∩ K) n : ℝ) / prefixCount K n +
        (Nat.card B : ℝ) / prefixCount K n := by
          norm_num [Nat.cast_add, add_div]

lemma relativeLowerDensity_remove_finite
    {D K B : Language} (hK : K.Infinite) (hB : B.Finite)
    (hden : (1 / 2 : ℝ) ≤
      GenLimit.PatientScope.relativeLowerDensity (D ∩ (K ∪ B)) (K ∪ B)) :
    (1 / 2 : ℝ) ≤ GenLimit.PatientScope.relativeLowerDensity (D ∩ K) K := by
  let expanded : ℕ → ℝ := relativeRatio (D ∩ (K ∪ B)) (K ∪ B)
  let original : ℕ → ℝ := relativeRatio (D ∩ K) K
  let err : ℕ → ℝ := fun n => (Nat.card B : ℝ) / prefixCount K n
  have hcountNat : Tendsto (fun n => prefixCount K n) atTop atTop :=
    prefixCount_tendsto_atTop hK
  have hcountReal : Tendsto (fun n => (prefixCount K n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hcountNat
  have herr : Tendsto err atTop (𝓝 0) := by
    exact hcountReal.const_div_atTop (Nat.card B : ℝ)
  have hpositive : ∀ᶠ n in atTop, 0 < prefixCount K n := by
    filter_upwards [hcountNat.eventually (eventually_ge_atTop 1)] with n hn
    omega
  have hcompare : ∀ᶠ n in atTop, expanded n ≤ original n + err n := by
    filter_upwards [hpositive] with n hn
    exact relativeRatio_finite_extension_le hB hn
  change (1 / 2 : ℝ) ≤ liminf original atTop
  change (1 / 2 : ℝ) ≤ liminf expanded atTop at hden
  have horigBdd : IsBoundedUnder (fun x y : ℝ => x ≥ y) atTop original :=
    isBoundedUnder_of_eventually_ge (Eventually.of_forall (fun n => relativeRatio_nonneg _ _ n))
  have hexpBdd : IsBoundedUnder (fun x y : ℝ => x ≥ y) atTop expanded :=
    isBoundedUnder_of_eventually_ge (Eventually.of_forall (fun n => relativeRatio_nonneg _ _ n))
  have horigLeOne : ∀ᶠ n in atTop, original n ≤ 1 := by
    filter_upwards [hpositive] with n hn
    unfold original relativeRatio
    apply (div_le_one (by exact_mod_cast hn)).2
    exact_mod_cast prefixCount_mono_set (A := D ∩ K) (C := K)
      (by intro x hx; exact hx.2) n
  have horigCobounded : IsCoboundedUnder (fun x y : ℝ => x ≥ y) atTop original :=
    isCoboundedUnder_ge_of_eventually_le atTop horigLeOne
  rw [Filter.le_liminf_iff' (u := original) horigCobounded horigBdd]
  intro y hy
  let z : ℝ := (y + (1 / 2 : ℝ)) / 2
  have hyz : y < z := by
    dsimp [z]
    linarith
  have hzhalf : z < (1 / 2 : ℝ) := by
    dsimp [z]
    linarith
  have hzlim : z < liminf expanded atTop := lt_of_lt_of_le hzhalf hden
  have heventExpanded : ∀ᶠ n in atTop, z < expanded n :=
    eventually_lt_of_lt_liminf hzlim hexpBdd
  have heventErr : ∀ᶠ n in atTop, err n < z - y :=
    (tendsto_order.mp herr).2 (z - y) (sub_pos.mpr hyz)
  filter_upwards [heventExpanded, heventErr, hcompare] with n hze herror hcomp
  linarith

end Stage3Case025
