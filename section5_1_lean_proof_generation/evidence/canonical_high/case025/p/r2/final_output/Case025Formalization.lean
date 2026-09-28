import Stage3Model
import Mathlib

open Filter
open scoped Topology
open GenLimit

namespace GenLimit.PatientScope

lemma prefixCount_mono {A B : Set ℕ} (h : A ⊆ B) (n : ℕ) :
    prefixCount A n ≤ prefixCount B n := by
  apply Finset.card_le_card
  intro x hx
  simp only [prefixFinset, Finset.mem_filter, Finset.mem_range] at hx ⊢
  exact ⟨hx.1, h hx.2⟩

lemma prefixCount_union_le (A B : Set ℕ) (n : ℕ) :
    prefixCount (A ∪ B) n ≤ prefixCount A n + prefixCount B n := by
  rw [prefixCount, prefixCount, prefixCount]
  rw [show prefixFinset (A ∪ B) n = prefixFinset A n ∪ prefixFinset B n by
    ext x
    simp only [prefixFinset, Finset.mem_union, Finset.mem_filter, Finset.mem_range, Set.mem_union]
    aesop]
  exact Finset.card_union_le _ _

lemma prefixCount_finite_le_card {F : Set ℕ} (hF : F.Finite) (n : ℕ) :
    prefixCount F n ≤ Nat.card F := by
  rw [Nat.card_eq_card_finite_toFinset hF]
  apply Finset.card_le_card
  intro x hx
  rw [hF.mem_toFinset]
  have hx' : x < n ∧ x ∈ F := by
    simpa only [prefixFinset, Finset.mem_filter, Finset.mem_range] using hx
  exact hx'.2

lemma prefixCount_inter_extension_le {Q K R : Set ℕ}
    (hfin : (R \ K).Finite) (n : ℕ) :
    prefixCount (Q ∩ R) n ≤ prefixCount (Q ∩ K) n + Nat.card (↥(R \ K)) := by
  calc
    prefixCount (Q ∩ R) n ≤ prefixCount ((Q ∩ K) ∪ (R \ K)) n := by
      apply prefixCount_mono
      intro x hx
      by_cases hxK : x ∈ K
      · exact Or.inl ⟨hx.1, hxK⟩
      · exact Or.inr ⟨hx.2, hxK⟩
    _ ≤ prefixCount (Q ∩ K) n + prefixCount (R \ K) n := prefixCount_union_le _ _ _
    _ ≤ prefixCount (Q ∩ K) n + Nat.card (↥(R \ K)) := Nat.add_le_add_left (prefixCount_finite_le_card hfin n) _

end GenLimit.PatientScope

namespace GenLimit.PatientScope

lemma density_ratio_extension_bound {Q K R : Set ℕ} (hKR : K ⊆ R)
    (hfin : (R \ K).Finite) {n : ℕ} (hpos : 0 < prefixCount K n) :
    (prefixCount (Q ∩ R) n : ℝ) / prefixCount R n -
        (Nat.card (↥(R \ K)) : ℝ) / prefixCount K n ≤
      (prefixCount (Q ∩ K) n : ℝ) / prefixCount K n := by
  have hkrCount : prefixCount K n ≤ prefixCount R n := prefixCount_mono hKR n
  have hrpos : (0 : ℝ) < prefixCount R n := by exact_mod_cast hpos.trans_le hkrCount
  have hkpos : (0 : ℝ) < prefixCount K n := by exact_mod_cast hpos
  have hbnonneg : (0 : ℝ) ≤ prefixCount (Q ∩ R) n := Nat.cast_nonneg _
  have hdenom :
      (prefixCount (Q ∩ R) n : ℝ) / prefixCount R n ≤
        (prefixCount (Q ∩ R) n : ℝ) / prefixCount K n := by
    exact div_le_div_of_nonneg_left hbnonneg hkpos (by exact_mod_cast hkrCount)
  have hnumNat := prefixCount_inter_extension_le (Q := Q) hfin n
  have hnum : (prefixCount (Q ∩ R) n : ℝ) ≤
      prefixCount (Q ∩ K) n + Nat.card (↥(R \ K)) := by exact_mod_cast hnumNat
  have hnumDiv :
      (prefixCount (Q ∩ R) n : ℝ) / prefixCount K n ≤
        (prefixCount (Q ∩ K) n + Nat.card (↥(R \ K)) : ℝ) / prefixCount K n := by
    exact (div_le_div_iff_of_pos_right hkpos).2 hnum
  calc
    (prefixCount (Q ∩ R) n : ℝ) / prefixCount R n -
        (Nat.card (↥(R \ K)) : ℝ) / prefixCount K n
      ≤ (prefixCount (Q ∩ R) n : ℝ) / prefixCount K n -
        (Nat.card (↥(R \ K)) : ℝ) / prefixCount K n := sub_le_sub_right hdenom _
    _ ≤ (prefixCount (Q ∩ K) n + Nat.card (↥(R \ K)) : ℝ) / prefixCount K n -
        (Nat.card (↥(R \ K)) : ℝ) / prefixCount K n := sub_le_sub_right hnumDiv _
    _ = (prefixCount (Q ∩ K) n : ℝ) / prefixCount K n := by ring

lemma prefixCount_tendsto_atTop {K : Set ℕ} (hK : K.Infinite) :
    Tendsto (fun n => prefixCount K n) atTop atTop := by
  rw [show (fun n => prefixCount K n) =
      (fun n => ∑ k ∈ Finset.range n, K.indicator (fun _ => (1 : ℕ)) k) by
        funext n
        simp [prefixCount, prefixFinset, Set.indicator]]
  exact (Set.infinite_iff_tendsto_sum_indicator_atTop (r := (1 : ℕ)) (by omega)).mp hK

end GenLimit.PatientScope

namespace GenLimit.PatientScope

lemma ratio_nonneg (A K : Set ℕ) (n : ℕ) :
    (0 : ℝ) ≤ (prefixCount A n : ℝ) / prefixCount K n := by positivity

lemma ratio_le_one {A K : Set ℕ} (hAK : A ⊆ K) (n : ℕ) :
    (prefixCount A n : ℝ) / prefixCount K n ≤ 1 := by
  by_cases hzero : prefixCount K n = 0
  · simp [hzero]
  · apply (div_le_one (by positivity)).2
    exact_mod_cast prefixCount_mono hAK n

lemma relativeLowerDensity_finite_extension {Q K R : Set ℕ}
    (hK : K.Infinite) (hKR : K ⊆ R) (hfin : (R \ K).Finite) :
    relativeLowerDensity (Q ∩ R) R ≤ relativeLowerDensity (Q ∩ K) K := by
  let u : ℕ → ℝ := fun n => (prefixCount (Q ∩ R) n : ℝ) / prefixCount R n
  let e : ℕ → ℝ := fun n => -((Nat.card (↥(R \ K)) : ℝ) / prefixCount K n)
  let v : ℕ → ℝ := fun n => (prefixCount (Q ∩ K) n : ℝ) / prefixCount K n
  have hkTop : Tendsto (fun n => prefixCount K n) atTop atTop := prefixCount_tendsto_atTop hK
  have hkCastTop : Tendsto (fun n => (prefixCount K n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hkTop
  have he : Tendsto e atTop (nhds 0) := by
    let c : ℝ := Nat.card (↥(R \ K))
    have hc : Tendsto (fun _ : ℕ => c) atTop (nhds c) := tendsto_const_nhds
    have hdiv := hc.div_atTop hkCastTop
    simpa [e, c] using hdiv.neg
  have hupos : ∀ n, 0 ≤ u n := by
    intro n
    exact ratio_nonneg _ _ _
  have hule : ∀ n, u n ≤ 1 := by
    intro n
    exact ratio_le_one (Set.inter_subset_right) n
  have huLower : IsBoundedUnder (fun x y : ℝ => x ≥ y) atTop u :=
    Filter.isBoundedUnder_of_eventually_ge (Filter.Eventually.of_forall hupos)
  have huUpper : IsBoundedUnder (fun x y : ℝ => x ≤ y) atTop u :=
    Filter.isBoundedUnder_of_eventually_le (Filter.Eventually.of_forall hule)
  have hsum : liminf u atTop + liminf e atTop ≤ liminf (u + e) atTop :=
    le_liminf_add huLower huUpper he.isBoundedUnder_ge he.isCoboundedUnder_ge
  have heInf : liminf e atTop = 0 := he.liminf_eq
  have hpoint : ∀ᶠ n in atTop, (u + e) n ≤ v n := by
    have hpositive : ∀ᶠ n in atTop, 0 < prefixCount K n := by
      filter_upwards [hkTop.eventually (eventually_ge_atTop 1)] with n hn
      omega
    filter_upwards [hpositive] with n hn
    simpa [u, e, v, Pi.add_apply, neg_div] using
      density_ratio_extension_bound (Q := Q) hKR hfin hn
  have hsumLower : IsBoundedUnder (fun x y : ℝ => x ≥ y) atTop (u + e) :=
    Filter.isBoundedUnder_ge_add huLower he.isBoundedUnder_ge
  have hvUpper : IsBoundedUnder (fun x y : ℝ => x ≤ y) atTop v := by
    apply Filter.isBoundedUnder_of_eventually_le
    apply Filter.Eventually.of_forall
    intro n
    exact ratio_le_one Set.inter_subset_right n
  have hlim : liminf (u + e) atTop ≤ liminf v atTop :=
    Filter.liminf_le_liminf hpoint hsumLower hvUpper.isCoboundedUnder_ge
  simpa [relativeLowerDensity, u, v, heInf] using hsum.trans hlim

end GenLimit.PatientScope

open Stage3Case025

namespace Stage3Case025

noncomputable def finiteExpansion (family : ℕ → Language) : ℕ → Language :=
  fun n =>
    let p := (Denumerable.eqv (ℕ × Finset ℕ)).symm n
    family p.1 ∪ (p.2 : Set ℕ)

lemma finiteExpansion_infinite (family : ℕ → Language) (hfamily : ∀ i, (family i).Infinite) :
    ∀ n, (finiteExpansion family n).Infinite := by
  intro n
  exact (hfamily ((Denumerable.eqv (ℕ × Finset ℕ)).symm n).1).mono Set.subset_union_left

lemma finiteExpansion_contains (family : ℕ → Language) (i : ℕ) (F : Finset ℕ) :
    ∃ n, finiteExpansion family n = family i ∪ (F : Set ℕ) := by
  let e := Denumerable.eqv (ℕ × Finset ℕ)
  refine ⟨e (i, F), ?_⟩
  simp [finiteExpansion, e]

lemma range_eq_target_union_badValues {input : Stream} {K : Language}
    (hcomplete : K ⊆ Set.range input)
    (hbad : GenLimit.Generic.FinitelyManyViolations input (fun x => x ∈ K)) :
    ∃ F : Set ℕ, F.Finite ∧ Set.range input = K ∪ F := by
  let V : Set ℕ := GenLimit.Generic.ViolationIndices input (fun x => x ∈ K)
  let F : Set ℕ := input '' V
  have hV : V.Finite := hbad
  have hF : F.Finite := hV.image input
  refine ⟨F, hF, Set.Subset.antisymm ?_ ?_⟩
  · intro x hx
    rcases hx with ⟨t, rfl⟩
    by_cases hxK : input t ∈ K
    · exact Or.inl hxK
    · exact Or.inr ⟨t, by simpa [V, GenLimit.Generic.ViolationIndices] using hxK, rfl⟩
  · intro x hx
    rcases hx with hxK | hxF
    · exact hcomplete hxK
    · rcases hxF with ⟨t, _, rfl⟩
      exact ⟨t, rfl⟩

lemma eventual_avoid_finite_of_eventual_injective
    {output : Stream} {B : Set ℕ} (hB : B.Finite) {T : ℕ}
    (hinj : ∀ t, T ≤ t → ∀ s, s < t → output s ≠ output t) :
    ∃ T', ∀ t, T' ≤ t → output t ∉ B := by
  let times : Set ℕ := {t | T ≤ t ∧ output t ∈ B}
  have hinjOn : Set.InjOn output times := by
    intro a ha b hb hab
    by_contra hne
    rcases lt_or_gt_of_ne hne with hablt | hbalt
    · exact (hinj b hb.1 a hablt) hab
    · exact (hinj a ha.1 b hbalt) hab.symm
  have himage : (output '' times).Finite := hB.subset (by
    intro x hx
    rcases hx with ⟨t, ht, rfl⟩
    exact ht.2)
  have htimes : times.Finite := Set.Finite.of_finite_image himage hinjOn
  obtain ⟨N, hN⟩ := htimes.exists_le
  refine ⟨max T (N + 1), ?_⟩
  intro t ht htB
  have htT : T ≤ t := le_trans (le_max_left _ _) ht
  have httimes : t ∈ times := ⟨htT, htB⟩
  have htN : t ≤ N := hN t httimes
  omega

lemma novel_transfer_finite_extension {input output : Stream} {K R : Language}
    (hfin : (R \ K).Finite)
    (hnovel : GenLimit.NovelGeneratesInLimit input output R) :
    GenLimit.NovelGeneratesInLimit input output K := by
  rcases hnovel with ⟨T, hT⟩
  obtain ⟨T', havoid⟩ := eventual_avoid_finite_of_eventual_injective hfin (fun t ht s hs => (hT t ht).2.2 s hs)
  refine ⟨max T T', ?_⟩
  intro t ht
  have htT : T ≤ t := le_trans (le_max_left _ _) ht
  have htT' : T' ≤ t := le_trans (le_max_right _ _) ht
  have hout := hT t htT
  refine ⟨?_, hout.2.1, hout.2.2⟩
  have houtR := hout.1
  have hnotBad := havoid t htT'
  exact by
    by_contra hnotK
    exact hnotBad ⟨houtR, hnotK⟩

 theorem finite_noise_transfer : FiniteNoiseTransferPrinciple := by
  intro hpositive
  intro family hfamily
  let expanded := finiteExpansion family
  have hexpanded : ∀ n, (expanded n).Infinite := finiteExpansion_infinite family hfamily
  obtain ⟨gen, hgen⟩ := hpositive expanded hexpanded
  refine ⟨gen, ?_⟩
  intro i input hpresentation
  rcases hpresentation with ⟨hcomplete, hviolations⟩
  obtain ⟨F, hFfinite, hrange⟩ := range_eq_target_union_badValues hcomplete hviolations
  obtain ⟨n, hn⟩ := finiteExpansion_contains family i hFfinite.toFinset
  have hFcoe : (hFfinite.toFinset : Set ℕ) = F := by ext x; simp
  have hexpandedEq : expanded n = Set.range input := by
    rw [show expanded n = finiteExpansion family n by rfl, hn, hFcoe, ← hrange]
  have hpresents : GenLimit.Presents input (expanded n) := hexpandedEq.symm
  obtain ⟨output, hfollows, hnovel, hdensity⟩ := hgen n input hpresents
  refine ⟨output, hfollows, ?_, ?_⟩
  · apply novel_transfer_finite_extension (K := family i) (R := expanded n)
    · rw [hexpandedEq, hrange]
      apply hFfinite.subset
      intro x hx
      rcases hx with ⟨hxUnion, hxNotK⟩
      exact hxUnion.resolve_left hxNotK
    · exact hnovel
  · apply hdensity.trans
    apply GenLimit.PatientScope.relativeLowerDensity_finite_extension
    · exact hfamily i
    · rw [hexpandedEq]
      exact hcomplete
    · rw [hexpandedEq, hrange]
      apply hFfinite.subset
      intro x hx
      rcases hx with ⟨hxUnion, hxNotK⟩
      exact hxUnion.resolve_left hxNotK

end Stage3Case025

theorem stage3_finite_noise_transfer : Stage3Case025.FiniteNoiseTransferPrinciple :=
  Stage3Case025.finite_noise_transfer
