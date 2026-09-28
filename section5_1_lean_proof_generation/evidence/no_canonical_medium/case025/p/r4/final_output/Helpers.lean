import Stage3Model
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Nat.Pairing

open Set Filter
open scoped Topology

namespace Stage3Case025

noncomputable def finiteAugmentedFamily (family : ℕ → Language) : ℕ → Language :=
  fun n => family n.unpair.1 ∪ (↑(Finset.equivBitIndices n.unpair.2) : Set ℕ)

lemma finiteAugmentedFamily_infinite
    (family : ℕ → Language) (hfamily : ∀ i, (family i).Infinite) :
    ∀ n, (finiteAugmentedFamily family n).Infinite := by
  intro n
  exact (hfamily n.unpair.1).mono subset_union_left

lemma violation_values_finite {input : Stream} {K : Language}
    (hbad : GenLimit.Generic.FinitelyManyViolations input (fun x => x ∈ K)) :
    (Set.range input \ K).Finite := by
  let V := GenLimit.Generic.ViolationIndices input (fun x => x ∈ K)
  have hV : V.Finite := hbad
  have hsub : Set.range input \ K ⊆ input '' V := by
    intro x hx
    rcases hx.1 with ⟨t, rfl⟩
    exact ⟨t, hx.2, rfl⟩
  exact (hV.image input).subset hsub

lemma range_eq_target_union_violations {input : Stream} {K : Language}
    (hcover : K ⊆ Set.range input) :
    Set.range input = K ∪ (Set.range input \ K) := by
  ext x
  constructor
  · intro hx
    by_cases hk : x ∈ K
    · exact Or.inl hk
    · exact Or.inr ⟨hx, hk⟩
  · intro hx
    rcases hx with hx | hx
    · exact hcover hx
    · exact hx.1

lemma range_is_finite_augmentation {input : Stream} {K : Language}
    (hpres : CompleteFiniteOccurrencePresentation input K) :
    ∃ code : ℕ, Set.range input = K ∪ (↑(Finset.equivBitIndices code) : Set ℕ) := by
  let B : Set ℕ := Set.range input \ K
  have hB : B.Finite := violation_values_finite hpres.2
  let s : Finset ℕ := hB.toFinset
  refine ⟨Finset.equivBitIndices.symm s, ?_⟩
  rw [Equiv.apply_symm_apply]
  simpa [B, s] using range_eq_target_union_violations hpres.1

end Stage3Case025

namespace Stage3Case025

lemma novelGeneratesInLimit_of_finite_union
    {input output : Stream} {K B : Language} (hB : B.Finite)
    (hnovel : GenLimit.NovelGeneratesInLimit input output (K ∪ B)) :
    GenLimit.NovelGeneratesInLimit input output K := by
  rcases hnovel with ⟨T, hT⟩
  let S : Set ℕ := {t | T ≤ t ∧ output t ∈ B}
  have hmaps : MapsTo output S B := by
    intro t ht
    exact ht.2
  have hinj : InjOn output S := by
    intro t ht u hu heq
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact (hT u hu.1).2.2 t hlt heq
    · exact (hT t ht.1).2.2 u hgt heq.symm
  have hS : S.Finite := hB.of_injOn hmaps hinj
  rcases hS.bddAbove with ⟨bound, hbound⟩
  refine ⟨max T (bound + 1), fun t ht => ?_⟩
  have htT : T ≤ t := le_trans (le_max_left _ _) ht
  have htBound : bound < t := lt_of_lt_of_le (Nat.lt_succ_self bound)
    (le_trans (le_max_right _ _) ht)
  have htNotB : output t ∉ B := by
    intro hout
    have htS : t ∈ S := ⟨htT, hout⟩
    exact (Nat.not_le_of_gt htBound) (hbound htS)
  rcases hT t htT with ⟨hout, hfresh, huniq⟩
  exact ⟨hout.resolve_right htNotB, hfresh, huniq⟩

end Stage3Case025

namespace Stage3Case025

lemma prefixCount_eq_sum_indicator (S : Set ℕ) (n : ℕ) :
    GenLimit.PatientScope.prefixCount S n =
      ∑ k ∈ Finset.range n, S.indicator (fun _ => 1) k := by
  classical
  rw [GenLimit.PatientScope.prefixCount, GenLimit.PatientScope.prefixFinset,
    Finset.card_eq_sum_ones]
  symm
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x hx
  simp only [Set.indicator]

lemma tendsto_prefixCount_atTop {K : Set ℕ} (hK : K.Infinite) :
    Tendsto (fun n => GenLimit.PatientScope.prefixCount K n) atTop atTop := by
  rw [show (fun n => GenLimit.PatientScope.prefixCount K n) =
      (fun n => ∑ k ∈ Finset.range n, K.indicator (fun _ => (1 : ℕ)) k) from
    funext (prefixCount_eq_sum_indicator K)]
  exact (Set.infinite_iff_tendsto_sum_indicator_atTop (R := ℕ) Nat.zero_lt_one).mp hK

end Stage3Case025

namespace Stage3Case025

lemma prefixCount_union_of_disjoint {S T : Set ℕ} (hST : Disjoint S T) (n : ℕ) :
    GenLimit.PatientScope.prefixCount (S ∪ T) n =
      GenLimit.PatientScope.prefixCount S n + GenLimit.PatientScope.prefixCount T n := by
  classical
  have hfin : Disjoint (GenLimit.PatientScope.prefixFinset S n)
      (GenLimit.PatientScope.prefixFinset T n) := by
    rw [Finset.disjoint_left]
    intro x hxS hxT
    have hxSmem : x ∈ S := (Finset.mem_filter.mp hxS).2
    have hxTmem : x ∈ T := (Finset.mem_filter.mp hxT).2
    exact Set.disjoint_left.mp hST hxSmem hxTmem
  rw [GenLimit.PatientScope.prefixCount, GenLimit.PatientScope.prefixCount,
    GenLimit.PatientScope.prefixCount]
  have hunion : GenLimit.PatientScope.prefixFinset (S ∪ T) n =
      GenLimit.PatientScope.prefixFinset S n ∪ GenLimit.PatientScope.prefixFinset T n := by
    ext x
    simp [GenLimit.PatientScope.prefixFinset, and_or_left]
  rw [hunion, Finset.card_union_of_disjoint hfin]

lemma eventually_prefixCount_eq_card {B : Set ℕ} (hB : B.Finite) :
    ∀ᶠ n in atTop, GenLimit.PatientScope.prefixCount B n = Nat.card B := by
  filter_upwards [Set.sum_indicator_eventually_eq_card (1 : ℕ) hB] with n hn
  rw [prefixCount_eq_sum_indicator]
  simpa using hn

end Stage3Case025

namespace Stage3Case025

/-- The analytic fact needed by the finite-noise reduction: adjoining finitely
many target points does not lower the relative density after restricting both
the numerator and denominator back to the original infinite target. -/
def FiniteDensityStability : Prop :=
  ∀ (A K B : Language), K.Infinite → B.Finite →
    (1 / 2 : ℝ) ≤ GenLimit.PatientScope.relativeLowerDensity (A ∩ (K ∪ B)) (K ∪ B) →
    (1 / 2 : ℝ) ≤ GenLimit.PatientScope.relativeLowerDensity (A ∩ K) K

lemma finiteNoiseTransfer_of_densityStability
    (hdensityStable : FiniteDensityStability) : FiniteNoiseTransferPrinciple := by
  intro hpositive family hfamily
  let augmented := finiteAugmentedFamily family
  have haugmented : ∀ n, (augmented n).Infinite :=
    finiteAugmentedFamily_infinite family hfamily
  rcases hpositive augmented haugmented with ⟨gen, hgen⟩
  refine ⟨gen, fun i input hpres => ?_⟩
  rcases range_is_finite_augmentation hpres with ⟨code, hrange⟩
  let index := Nat.pair i code
  have hindex : augmented index =
      family i ∪ (↑(Finset.equivBitIndices code) : Set ℕ) := by
    simp [augmented, finiteAugmentedFamily, index]
  have hpresents : GenLimit.Presents input (augmented index) := by
    rw [GenLimit.Presents, hindex]
    exact hrange
  rcases hgen index input hpresents with ⟨output, hfollows, hnovel, hdensity⟩
  refine ⟨output, hfollows, ?_, ?_⟩
  · rw [hindex] at hnovel
    exact novelGeneratesInLimit_of_finite_union
      (K := family i) (B := (↑(Finset.equivBitIndices code) : Set ℕ))
      (Finset.finite_toSet _) hnovel
  · rw [hindex] at hdensity
    exact hdensityStable (GenLimit.GeneratorFirst input output) (family i)
      (↑(Finset.equivBitIndices code) : Set ℕ) (hfamily i) (Finset.finite_toSet _) hdensity

end Stage3Case025

namespace Stage3Case025

lemma prefixCount_mono {S T : Set ℕ} (hST : S ⊆ T) (n : ℕ) :
    GenLimit.PatientScope.prefixCount S n ≤ GenLimit.PatientScope.prefixCount T n := by
  classical
  apply Finset.card_le_card
  intro x hx
  rw [GenLimit.PatientScope.prefixFinset, Finset.mem_filter] at hx ⊢
  exact ⟨hx.1, hST hx.2⟩

lemma prefixCount_union_le (S T : Set ℕ) (n : ℕ) :
    GenLimit.PatientScope.prefixCount (S ∪ T) n ≤
      GenLimit.PatientScope.prefixCount S n + GenLimit.PatientScope.prefixCount T n := by
  classical
  rw [GenLimit.PatientScope.prefixCount, GenLimit.PatientScope.prefixCount,
    GenLimit.PatientScope.prefixCount]
  have hunion : GenLimit.PatientScope.prefixFinset (S ∪ T) n =
      GenLimit.PatientScope.prefixFinset S n ∪ GenLimit.PatientScope.prefixFinset T n := by
    ext x
    simp [GenLimit.PatientScope.prefixFinset, and_or_left]
  rw [hunion]
  exact Finset.card_union_le _ _

lemma relativeRatio_nonneg (A K : Set ℕ) (n : ℕ) :
    (0 : ℝ) ≤ (GenLimit.PatientScope.prefixCount (A ∩ K) n : ℝ) /
      GenLimit.PatientScope.prefixCount K n := by positivity

lemma relativeRatio_le_one (A K : Set ℕ) (n : ℕ) :
    (GenLimit.PatientScope.prefixCount (A ∩ K) n : ℝ) /
      GenLimit.PatientScope.prefixCount K n ≤ 1 := by
  by_cases hzero : GenLimit.PatientScope.prefixCount K n = 0
  · simp [hzero]
  · apply (div_le_one (by positivity)).2
    exact_mod_cast prefixCount_mono inter_subset_right n

end Stage3Case025

namespace Stage3Case025

lemma finiteDensityStability : FiniteDensityStability := by
  intro A K B hK hB hdensity
  let rLarge : ℕ → ℝ := fun n =>
    (GenLimit.PatientScope.prefixCount (A ∩ (K ∪ B)) n : ℝ) /
      GenLimit.PatientScope.prefixCount (K ∪ B) n
  let rSmall : ℕ → ℝ := fun n =>
    (GenLimit.PatientScope.prefixCount (A ∩ K) n : ℝ) /
      GenLimit.PatientScope.prefixCount K n
  let err : ℕ → ℝ := fun n =>
    (Nat.card B : ℝ) / GenLimit.PatientScope.prefixCount K n
  have hdenNat := tendsto_prefixCount_atTop hK
  have hdenReal : Tendsto (fun n => (GenLimit.PatientScope.prefixCount K n : ℝ))
      atTop atTop := tendsto_natCast_atTop_atTop.comp hdenNat
  have herr : Tendsto err atTop (𝓝 0) := by
    exact hdenReal.const_div_atTop (Nat.card B : ℝ)
  have hpositive : ∀ᶠ n in atTop, 0 < GenLimit.PatientScope.prefixCount K n := by
    filter_upwards [Filter.tendsto_atTop.1 hdenNat 1] with n hn
    omega
  have hBcount := eventually_prefixCount_eq_card hB
  have hcompare : ∀ᶠ n in atTop, rLarge n ≤ rSmall n + err n := by
    filter_upwards [hpositive, hBcount] with n hnpos hnB
    have hsubset : A ∩ (K ∪ B) ⊆ (A ∩ K) ∪ B := by
      intro x hx
      rcases hx.2 with hxK | hxB
      · exact Or.inl ⟨hx.1, hxK⟩
      · exact Or.inr hxB
    have hnumNat : GenLimit.PatientScope.prefixCount (A ∩ (K ∪ B)) n ≤
        GenLimit.PatientScope.prefixCount (A ∩ K) n +
          GenLimit.PatientScope.prefixCount B n :=
      (prefixCount_mono hsubset n).trans (prefixCount_union_le (A ∩ K) B n)
    have hdenNat' : GenLimit.PatientScope.prefixCount K n ≤
        GenLimit.PatientScope.prefixCount (K ∪ B) n :=
      prefixCount_mono subset_union_left n
    have hratio : rLarge n ≤
        ((GenLimit.PatientScope.prefixCount (A ∩ K) n : ℝ) +
          GenLimit.PatientScope.prefixCount B n) /
            GenLimit.PatientScope.prefixCount K n := by
      dsimp [rLarge]
      apply div_le_div₀
      · positivity
      · exact_mod_cast hnumNat
      · exact_mod_cast hnpos
      · exact_mod_cast hdenNat'
    calc
      rLarge n ≤ ((GenLimit.PatientScope.prefixCount (A ∩ K) n : ℝ) +
          GenLimit.PatientScope.prefixCount B n) /
            GenLimit.PatientScope.prefixCount K n := hratio
      _ = rSmall n + err n := by
        dsimp [rSmall, err]
        rw [hnB, Nat.card_coe_set_eq]
        ring
  rw [GenLimit.PatientScope.relativeLowerDensity] at hdensity ⊢
  change (1 / 2 : ℝ) ≤ Filter.liminf rLarge atTop at hdensity
  change (1 / 2 : ℝ) ≤ Filter.liminf rSmall atTop
  apply le_of_forall_lt
  intro c hc
  let mid : ℝ := (c + (1 / 2 : ℝ)) / 2
  let high : ℝ := (mid + (1 / 2 : ℝ)) / 2
  have hcmid : c < mid := by dsimp [mid]; linarith
  have hmidhigh : mid < high := by dsimp [high, mid]; linarith
  have hhighhalf : high < (1 / 2 : ℝ) := by dsimp [high, mid]; linarith
  have hhighlim : high < Filter.liminf rLarge atTop := hhighhalf.trans_le hdensity
  have hlowerLarge : Filter.IsBoundedUnder (fun x y : ℝ => x ≥ y) atTop rLarge := by
    apply Filter.isBoundedUnder_of_eventually_ge
    exact Filter.Eventually.of_forall fun n => relativeRatio_nonneg A (K ∪ B) n
  have heventLarge : ∀ᶠ n in atTop, high < rLarge n :=
    Filter.eventually_lt_of_lt_liminf hhighlim hlowerLarge
  have heventErr : ∀ᶠ n in atTop, err n < high - mid := by
    exact (tendsto_order.1 herr).2 (high - mid) (sub_pos.mpr hmidhigh)
  have heventSmall : ∀ᶠ n in atTop, mid ≤ rSmall n := by
    filter_upwards [heventLarge, heventErr, hcompare] with n hnLarge hnErr hnCompare
    linarith
  have hupperSmall : Filter.IsCoboundedUnder (fun x y : ℝ => x ≥ y) atTop rSmall := by
    apply isCoboundedUnder_ge_of_eventually_le atTop
    exact Filter.Eventually.of_forall fun n => relativeRatio_le_one A K n
  have hmidL : mid ≤ Filter.liminf rSmall atTop :=
    Filter.le_liminf_of_le (a := mid) hupperSmall heventSmall
  exact hcmid.trans_le hmidL

end Stage3Case025

namespace Stage3Case025

theorem finiteNoiseTransfer : FiniteNoiseTransferPrinciple :=
  finiteNoiseTransfer_of_densityStability finiteDensityStability

end Stage3Case025
