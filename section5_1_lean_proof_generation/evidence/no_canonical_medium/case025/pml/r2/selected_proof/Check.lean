import Stage3Model
import Mathlib.Topology.Algebra.Order.LiminfLimsup

open Filter
open scoped Topology

namespace Test

open GenLimit.PatientScope

lemma prefixCount_aug_le (A K : Set ℕ) (F : Finset ℕ) (n : ℕ) :
    prefixCount (A ∩ (K ∪ (F : Set ℕ))) n ≤
      prefixCount (A ∩ K) n + F.card := by
  classical
  unfold prefixCount
  let X := prefixFinset (A ∩ (K ∪ (F : Set ℕ))) n
  let Y := prefixFinset (A ∩ K) n
  have hsub : X ⊆ Y ∪ F := by
    intro x hx
    simp only [X, Y, Finset.mem_union, mem_prefixFinset] at hx ⊢
    rcases hx with ⟨hxn, hxA, hxK | hxF⟩
    · exact Or.inl ⟨hxn, hxA, hxK⟩
    · exact Or.inr hxF
  exact (Finset.card_le_card hsub).trans (Finset.card_union_le Y F)

lemma finite_union_density_transfer (A K : Set ℕ) (hK : K.Infinite) (F : Finset ℕ) :
    relativeLowerDensity (A ∩ (K ∪ (F : Set ℕ))) (K ∪ (F : Set ℕ)) ≤
      relativeLowerDensity (A ∩ K) K := by
  let u : ℕ → ℝ := fun n =>
    (prefixCount (A ∩ K) n : ℝ) / (prefixCount K n : ℝ)
  let v : ℕ → ℝ := fun n =>
    (prefixCount (A ∩ (K ∪ (F : Set ℕ))) n : ℝ) /
      (prefixCount (K ∪ (F : Set ℕ)) n : ℝ)
  let e : ℕ → ℝ := fun n => (F.card : ℝ) / (prefixCount K n : ℝ)
  have hcount := tendsto_prefixCount_atTop hK
  have hcountR : Tendsto (fun n => (prefixCount K n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hcount
  have he : Tendsto e atTop (𝓝 0) := by
    simpa [e] using hcountR.const_div_atTop (F.card : ℝ)
  have hKpos : ∀ᶠ n : ℕ in atTop, 0 < prefixCount K n :=
    hcount.eventually (eventually_gt_atTop 0)
  have hv_le : ∀ᶠ n : ℕ in atTop, v n ≤ u n + e n := by
    filter_upwards [hKpos] with n hn
    have hnR : (0 : ℝ) < prefixCount K n := by exact_mod_cast hn
    have hden : (prefixCount K n : ℝ) ≤ prefixCount (K ∪ (F : Set ℕ)) n := by
      exact_mod_cast prefixCount_mono (Set.subset_union_left) n
    have hnum : (prefixCount (A ∩ (K ∪ (F : Set ℕ))) n : ℝ) ≤
        prefixCount (A ∩ K) n + F.card := by
      exact_mod_cast prefixCount_aug_le A K F n
    dsimp [u, v, e]
    calc
      (prefixCount (A ∩ (K ∪ (F : Set ℕ))) n : ℝ) /
          (prefixCount (K ∪ (F : Set ℕ)) n : ℝ)
          ≤ (prefixCount (A ∩ (K ∪ (F : Set ℕ))) n : ℝ) /
              (prefixCount K n : ℝ) := by
                apply div_le_div_of_nonneg_left
                · positivity
                · exact hnR
                · exact hden
      _ ≤ ((prefixCount (A ∩ K) n : ℝ) + F.card) /
              (prefixCount K n : ℝ) :=
            div_le_div_of_nonneg_right hnum hnR.le
      _ = (prefixCount (A ∩ K) n : ℝ) / (prefixCount K n : ℝ) +
              (F.card : ℝ) / (prefixCount K n : ℝ) := by rw [add_div]
  have hu_nonneg : ∀ n, 0 ≤ u n := by intro n; positivity
  have hu_le_one : ∀ n, u n ≤ 1 := by
    intro n
    dsimp [u]
    by_cases hn : prefixCount K n = 0
    · simp [hn]
    · rw [div_le_one (by positivity)]
      exact_mod_cast prefixCount_mono Set.inter_subset_right n
  have hv_nonneg : ∀ n, 0 ≤ v n := by intro n; positivity
  have hu_above : IsBoundedUnder (· ≤ ·) atTop u :=
    isBoundedUnder_of_eventually_le (Eventually.of_forall hu_le_one)
  have hue_bddAbove : IsCoboundedUnder (· ≥ ·) atTop (fun n => u n + e n) := by
    simpa only [Pi.add_apply] using
      isCoboundedUnder_ge_add hu_above he.isCoboundedUnder_ge
  have hfirst : liminf v atTop ≤ liminf (fun n => u n + e n) atTop :=
    liminf_le_liminf hv_le
      (isBoundedUnder_of_eventually_ge (Eventually.of_forall hv_nonneg))
      hue_bddAbove
  have he_below := he.isBoundedUnder_ge
  have he_above := he.isBoundedUnder_le
  have hu_below : IsBoundedUnder (· ≥ ·) atTop u :=
    isBoundedUnder_of_eventually_ge (Eventually.of_forall hu_nonneg)
  have hu_cobelow : IsCoboundedUnder (· ≥ ·) atTop u :=
    isCoboundedUnder_ge_of_le atTop hu_le_one
  have hadd : liminf (fun n => e n + u n) atTop ≤ limsup e atTop + liminf u atTop :=
    liminf_add_le he_below he_above hu_below hu_cobelow
  have hsecond : liminf (fun n => u n + e n) atTop ≤ liminf u atTop := by
    rw [liminf_congr (Eventually.of_forall fun n => add_comm (u n) (e n))]
    simpa [he.limsup_eq] using hadd
  change liminf v atTop ≤ liminf u atTop
  exact hfirst.trans hsecond

end Test

open Stage3Case025

namespace Test

noncomputable def decodeFinset (n : ℕ) : Finset ℕ :=
  ((Encodable.decode n : Option (List ℕ)).getD []).toFinset

noncomputable def augmentedFamily (family : ℕ → Language) (n : ℕ) : Language :=
  family (Nat.unpair n).1 ∪ (decodeFinset (Nat.unpair n).2 : Set ℕ)

lemma augmentedFamily_infinite (family : ℕ → Language)
    (hinf : ∀ i, (family i).Infinite) (n : ℕ) :
    (augmentedFamily family n).Infinite := by
  exact (hinf (Nat.unpair n).1).mono Set.subset_union_left

lemma decodeFinset_encode (F : Finset ℕ) :
    decodeFinset (Encodable.encode F.toList) = F := by
  simp [decodeFinset]

lemma augmentedFamily_pair (family : ℕ → Language) (i : ℕ) (F : Finset ℕ) :
    augmentedFamily family (Nat.pair i (Encodable.encode F.toList)) =
      family i ∪ (F : Set ℕ) := by
  simp [augmentedFamily, Nat.unpair_pair, decodeFinset_encode]

lemma stage3_finite_noise_transfer_test : FiniteNoiseTransferPrinciple := by
  intro positive family hinf
  let enlarged : ℕ → Language := augmentedFamily family
  have henlarged : ∀ j, (enlarged j).Infinite := by
    intro j
    exact augmentedFamily_infinite family hinf j
  obtain ⟨gen, hgen⟩ := positive enlarged henlarged
  refine ⟨gen, ?_⟩
  intro i input hP
  let K := family i
  have hvalues : (Set.range input \ K).Finite := by
    rw [GenLimit.Generic.valuesOutside_eq_image_violationIndices]
    exact hP.2.image input
  let F : Finset ℕ := hvalues.toFinset
  have hF : (F : Set ℕ) = Set.range input \ K := by
    simp [F]
  let j := Nat.pair i (Encodable.encode F.toList)
  have henlarged_j : enlarged j = K ∪ (F : Set ℕ) := by
    simpa [enlarged, j, K] using augmentedFamily_pair family i F
  have hrange : Set.range input = K ∪ (F : Set ℕ) := by
    rw [hF]
    ext x
    constructor
    · intro hx
      by_cases hxK : x ∈ K
      · exact Or.inl hxK
      · exact Or.inr ⟨hx, hxK⟩
    · rintro (hxK | ⟨hx, -⟩)
      · exact hP.1 hxK
      · exact hx
  have hpresents : GenLimit.Presents input (enlarged j) := by
    rw [henlarged_j]
    exact hrange
  obtain ⟨output, hfollows, hnovel, hdensity⟩ := hgen j input hpresents
  refine ⟨output, hfollows, ?_, ?_⟩
  · obtain ⟨T, hT⟩ := hnovel
    obtain ⟨B, hB⟩ := hP.2.bddAbove
    refine ⟨max T (B + 1), ?_⟩
    intro t ht
    have htT : T ≤ t := le_trans (le_max_left _ _) ht
    have htB : B + 1 ≤ t := le_trans (le_max_right _ _) ht
    obtain ⟨hmem, hfresh, hdistinct⟩ := hT t htT
    refine ⟨?_, hfresh, hdistinct⟩
    rw [henlarged_j] at hmem
    rcases hmem with hmemK | hmemF
    · exact hmemK
    · exfalso
      have houtside : output t ∈ Set.range input \ K := by
        rw [← hF]
        exact hmemF
      obtain ⟨s, hsout⟩ := houtside.1
      have hsviol : s ∈ GenLimit.Generic.ViolationIndices input (fun x => x ∈ K) := by
        change ¬ input s ∈ K
        simpa [hsout] using houtside.2
      have hsB : s ≤ B := hB hsviol
      apply hfresh
      rw [GenLimit.mem_sample_iff]
      exact ⟨s, Nat.lt.step (lt_of_le_of_lt hsB (lt_of_lt_of_le (Nat.lt_succ_self B) htB)), hsout⟩
  · have htransfer := finite_union_density_transfer
      (GenLimit.GeneratorFirst input output) K (hinf i) F
    rw [← henlarged_j] at htransfer
    exact hdensity.trans htransfer

end Test
