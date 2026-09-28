import Stage3Model
import Mathlib

open Set Filter
open scoped Topology

namespace Stage3Case025Formalization

noncomputable def decodeFinset (n : ℕ) : Finset ℕ :=
  (Encodable.decode n).getD ∅

@[simp] theorem decodeFinset_encode (F : Finset ℕ) :
    decodeFinset (Encodable.encode F) = F := by
  simp [decodeFinset, Encodable.encodek]

noncomputable def finiteExtensionFamily
    (family : ℕ → Stage3Case025.Language) : ℕ → Stage3Case025.Language :=
  fun n => family (Nat.unpair n).1 ∪ (decodeFinset (Nat.unpair n).2 : Set ℕ)

@[simp] theorem finiteExtensionFamily_pair
    (family : ℕ → Stage3Case025.Language) (i : ℕ) (F : Finset ℕ) :
    finiteExtensionFamily family (Nat.pair i (Encodable.encode F)) =
      family i ∪ (F : Set ℕ) := by
  simp [finiteExtensionFamily]

 theorem finiteExtensionFamily_infinite
    {family : ℕ → Stage3Case025.Language}
    (hfamily : ∀ i, (family i).Infinite) :
    ∀ n, (finiteExtensionFamily family n).Infinite := by
  intro n
  exact (hfamily (Nat.unpair n).1).mono subset_union_left

 theorem finite_bad_values
    {input : Stage3Case025.Stream} {K : Stage3Case025.Language}
    (hnoise : GenLimit.Generic.FinitelyManyViolations input (fun x => x ∈ K)) :
    (Set.range input \ K).Finite := by
  let badTimes : Set ℕ := GenLimit.Generic.ViolationIndices input (fun x => x ∈ K)
  have hbad : badTimes.Finite := hnoise
  have himage : (input '' badTimes).Finite := hbad.image input
  apply himage.subset
  intro x hx
  rcases hx with ⟨⟨t, rfl⟩, htK⟩
  refine ⟨t, ?_, rfl⟩
  exact htK

 theorem range_eq_union_bad
    {input : Stage3Case025.Stream} {K : Stage3Case025.Language}
    (hcomplete : K ⊆ Set.range input) :
    Set.range input = K ∪ (Set.range input \ K) := by
  ext x
  constructor
  · intro hx
    by_cases hxK : x ∈ K
    · exact Or.inl hxK
    · exact Or.inr ⟨hx, hxK⟩
  · rintro (hx | hx)
    · exact hcomplete hx
    · exact hx.1

 theorem presents_finite_extension
    {family : ℕ → Stage3Case025.Language}
    {i : ℕ} {input : Stage3Case025.Stream}
    (hpresent : Stage3Case025.CompleteFiniteOccurrencePresentation input (family i)) :
    ∃ code, GenLimit.Presents input (finiteExtensionFamily family code) := by
  rcases hpresent with ⟨hcomplete, hnoise⟩
  have hfinite := finite_bad_values hnoise
  let F : Finset ℕ := hfinite.toFinset
  refine ⟨Nat.pair i (Encodable.encode F), ?_⟩
  unfold GenLimit.Presents
  rw [finiteExtensionFamily_pair]
  rw [range_eq_union_bad hcomplete]
  congr 1
  ext x
  simp [F]

end Stage3Case025Formalization

namespace Stage3Case025Formalization

 theorem eventually_avoid_finite_of_eventual_norepeat
    {output : ℕ → ℕ} {F : Set ℕ}
    (hF : F.Finite)
    (hnorepeat : ∃ T, ∀ t, T ≤ t → ∀ s, s < t → output s ≠ output t) :
    ∃ T', ∀ t, T' ≤ t → output t ∉ F := by
  rcases hnorepeat with ⟨T, hnorepeat⟩
  let times : Set ℕ := {t | T ≤ t ∧ output t ∈ F}
  have hinj : Set.InjOn output times := by
    intro a ha b hb hab
    rcases lt_trichotomy a b with hablt | habeq | hbalt
    · exact False.elim ((hnorepeat b hb.1 a hablt) hab)
    · exact habeq
    · exact False.elim ((hnorepeat a ha.1 b hbalt) hab.symm)
  have htimes : times.Finite := by
    apply Set.Finite.of_finite_image (f := output) _ hinj
    exact hF.subset (Set.image_subset_iff.mpr fun t ht => ht.2)
  rcases htimes.exists_le with ⟨M, hM⟩
  refine ⟨max T (M + 1), ?_⟩
  intro t ht htF
  have htT : T ≤ t := le_trans (le_max_left _ _) ht
  have httimes : t ∈ times := ⟨htT, htF⟩
  have htleM := hM t httimes
  have hMlt : M < t := lt_of_lt_of_le (Nat.lt_succ_self M) (le_trans (le_max_right _ _) ht)
  omega

 theorem novel_transfer_of_finite_extension
    {input output : Stage3Case025.Stream}
    {K R : Stage3Case025.Language}
    (hfinite : (R \ K).Finite)
    (hnovel : GenLimit.NovelGeneratesInLimit input output R) :
    GenLimit.NovelGeneratesInLimit input output K := by
  rcases hnovel with ⟨T, hT⟩
  have havoid : ∃ T', ∀ t, T' ≤ t → output t ∉ R \ K := by
    apply eventually_avoid_finite_of_eventual_norepeat hfinite
    exact ⟨T, fun t ht => (hT t ht).2.2⟩
  rcases havoid with ⟨T', hT'⟩
  refine ⟨max T T', ?_⟩
  intro t ht
  have htT : T ≤ t := le_trans (le_max_left _ _) ht
  have htT' : T' ≤ t := le_trans (le_max_right _ _) ht
  rcases hT t htT with ⟨houtR, hfresh, hnorepeat⟩
  refine ⟨?_, hfresh, hnorepeat⟩
  by_contra houtK
  exact hT' t htT' ⟨houtR, houtK⟩

end Stage3Case025Formalization

namespace Stage3Case025Formalization

open GenLimit.PatientScope

 theorem prefixFinset_mono {A B : Set ℕ} (hAB : A ⊆ B) (n : ℕ) :
    prefixFinset A n ⊆ prefixFinset B n := by
  intro x hx
  simp only [prefixFinset, Finset.mem_filter, Finset.mem_range] at hx ⊢
  exact ⟨hx.1, hAB hx.2⟩

 theorem prefixCount_mono {A B : Set ℕ} (hAB : A ⊆ B) (n : ℕ) :
    prefixCount A n ≤ prefixCount B n := by
  exact Finset.card_le_card (prefixFinset_mono hAB n)

 theorem prefixFinset_union_subset (A B : Set ℕ) (n : ℕ) :
    prefixFinset (A ∪ B) n ⊆ prefixFinset A n ∪ prefixFinset B n := by
  intro x hx
  simp only [prefixFinset, Finset.mem_filter, Finset.mem_range, Finset.mem_union] at hx ⊢
  rcases hx.2 with hxA | hxB
  · exact Or.inl ⟨hx.1, hxA⟩
  · exact Or.inr ⟨hx.1, hxB⟩

 theorem prefixCount_union_le (A B : Set ℕ) (n : ℕ) :
    prefixCount (A ∪ B) n ≤ prefixCount A n + prefixCount B n := by
  calc
    prefixCount (A ∪ B) n ≤ (prefixFinset A n ∪ prefixFinset B n).card :=
      Finset.card_le_card (prefixFinset_union_subset A B n)
    _ ≤ prefixCount A n + prefixCount B n := Finset.card_union_le _ _

 theorem prefixCount_le_ncard {F : Set ℕ} (hF : F.Finite) (n : ℕ) :
    prefixCount F n ≤ F.ncard := by
  change (prefixFinset F n).card ≤ F.ncard
  rw [← Set.ncard_coe_finset]
  apply Set.ncard_le_ncard _ hF
  intro x hx
  have hx' : x < n ∧ x ∈ F := by simpa [prefixFinset] using hx
  exact hx'.2

 theorem prefixCount_tendsto_atTop {K : Set ℕ} (hK : K.Infinite) :
    Tendsto (prefixCount K) atTop atTop := by
  apply Filter.tendsto_atTop.mpr
  intro m
  rcases hK.exists_subset_card_eq m with ⟨s, hsK, hscard⟩
  by_cases hs : s.Nonempty
  · let N := s.max' hs + 1
    filter_upwards [eventually_ge_atTop N] with n hn
    have hsubset : s ⊆ prefixFinset K n := by
      intro x hx
      simp only [prefixFinset, Finset.mem_filter, Finset.mem_range]
      refine ⟨?_, hsK hx⟩
      have hxmax : x ≤ s.max' hs := Finset.le_max' s x hx
      omega
    rw [← hscard]
    exact Finset.card_le_card hsubset
  · have sempty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    have hm : m = 0 := by simpa [sempty] using hscard.symm
    simp [hm]

 theorem ratio_bounded_below (A K : Set ℕ) :
    IsBoundedUnder (fun x y : ℝ => x ≥ y) atTop
      (fun n => (prefixCount A n : ℝ) / (prefixCount K n : ℝ)) := by
  apply Filter.isBoundedUnder_of_eventually_ge (a := 0)
  exact Filter.Eventually.of_forall fun n =>
    div_nonneg (by exact_mod_cast (Nat.zero_le (prefixCount A n)))
      (by exact_mod_cast (Nat.zero_le (prefixCount K n)))

 theorem ratio_le_one (A K : Set ℕ) (hAK : A ⊆ K) :
    ∀ n, (prefixCount A n : ℝ) / (prefixCount K n : ℝ) ≤ 1 := by
  intro n
  have hcount := prefixCount_mono hAK n
  by_cases hz : prefixCount K n = 0
  · have hzA : prefixCount A n = 0 := Nat.eq_zero_of_le_zero (hz ▸ hcount)
    simp [hz, hzA]
  · apply (div_le_one (by exact_mod_cast (Nat.pos_of_ne_zero hz))).2
    exact_mod_cast hcount

 theorem ratio_cobounded_above (A K : Set ℕ) (hAK : A ⊆ K) :
    IsCoboundedUnder (fun x y : ℝ => x ≥ y) atTop
      (fun n => (prefixCount A n : ℝ) / (prefixCount K n : ℝ)) := by
  apply Filter.isCoboundedUnder_ge_of_eventually_le atTop
  exact Filter.Eventually.of_forall (ratio_le_one A K hAK)

 theorem finite_extension_ratio_approx
    {Q K R : Set ℕ}
    (hK : K.Infinite) (hKR : K ⊆ R) (hfinite : (R \ K).Finite) :
    ∀ᶠ n in atTop,
      (prefixCount (Q ∩ R) n : ℝ) / (prefixCount R n : ℝ) ≤
        (prefixCount (Q ∩ K) n : ℝ) / (prefixCount K n : ℝ) +
          (R \ K).ncard / (prefixCount K n : ℝ) := by
  have hpos : ∀ᶠ n in atTop, 0 < prefixCount K n :=
    (prefixCount_tendsto_atTop hK).eventually (eventually_gt_atTop 0)
  filter_upwards [hpos] with n hn
  have hnumset : Q ∩ R ⊆ (Q ∩ K) ∪ (R \ K) := by
    intro x hx
    by_cases hxK : x ∈ K
    · exact Or.inl ⟨hx.1, hxK⟩
    · exact Or.inr ⟨hx.2, hxK⟩
  have hnumNat : prefixCount (Q ∩ R) n ≤
      prefixCount (Q ∩ K) n + (R \ K).ncard := by
    calc
      prefixCount (Q ∩ R) n ≤ prefixCount ((Q ∩ K) ∪ (R \ K)) n :=
        prefixCount_mono hnumset n
      _ ≤ prefixCount (Q ∩ K) n + prefixCount (R \ K) n :=
        prefixCount_union_le _ _ _
      _ ≤ prefixCount (Q ∩ K) n + (R \ K).ncard :=
        Nat.add_le_add_left (prefixCount_le_ncard hfinite n) _
  have hdenNat : prefixCount K n ≤ prefixCount R n := prefixCount_mono hKR n
  have hKposR : (0 : ℝ) < prefixCount K n := by exact_mod_cast hn
  calc
    (prefixCount (Q ∩ R) n : ℝ) / (prefixCount R n : ℝ)
        ≤ (prefixCount (Q ∩ R) n : ℝ) / (prefixCount K n : ℝ) := by
            gcongr
    _ ≤ ((prefixCount (Q ∩ K) n + (R \ K).ncard : ℕ) : ℝ) /
          (prefixCount K n : ℝ) := by
            gcongr
    _ = (prefixCount (Q ∩ K) n : ℝ) / (prefixCount K n : ℝ) +
          (R \ K).ncard / (prefixCount K n : ℝ) := by
            push_cast
            ring

 theorem finite_perturbation_relativeLowerDensity
    {Q K R : Set ℕ}
    (hK : K.Infinite) (hKR : K ⊆ R) (hfinite : (R \ K).Finite) :
    relativeLowerDensity (Q ∩ R) R ≤ relativeLowerDensity (Q ∩ K) K := by
  unfold relativeLowerDensity
  apply le_of_forall_lt
  intro b hb
  let c : ℝ := ((R \ K).ncard : ℝ)
  let mid : ℝ := (b + Filter.liminf
    (fun n : ℕ => (prefixCount (Q ∩ R) n : ℝ) / (prefixCount R n : ℝ)) atTop) / 2
  have hbmid : b < mid := by dsimp [mid]; linarith
  have hmidlim : mid < Filter.liminf
      (fun n : ℕ => (prefixCount (Q ∩ R) n : ℝ) / (prefixCount R n : ℝ)) atTop := by
    dsimp [mid]
    linarith
  have hR_event : ∀ᶠ n in atTop, mid <
      (prefixCount (Q ∩ R) n : ℝ) / (prefixCount R n : ℝ) :=
    Filter.eventually_lt_of_lt_liminf hmidlim (ratio_bounded_below _ _)
  have herror : Tendsto (fun n : ℕ => c / (prefixCount K n : ℝ)) atTop (nhds 0) := by
    apply tendsto_const_nhds.div_atTop
    exact (tendsto_natCast_atTop_atTop.comp (prefixCount_tendsto_atTop hK))
  have herr_event : ∀ᶠ n in atTop, c / (prefixCount K n : ℝ) < mid - b := by
    have hpos : 0 < mid - b := sub_pos.mpr hbmid
    exact (tendsto_order.1 herror).2 _ hpos
  have happrox := finite_extension_ratio_approx (Q := Q) hK hKR hfinite
  let lower : ℝ := (b + mid) / 2
  have hblower : b < lower := by dsimp [lower]; linarith
  have hlower_event : ∀ᶠ n in atTop, lower <
      (prefixCount (Q ∩ K) n : ℝ) / (prefixCount K n : ℝ) := by
    have herr_event' : ∀ᶠ n in atTop, c / (prefixCount K n : ℝ) < mid - lower := by
      have hpos : 0 < mid - lower := by dsimp [lower]; linarith
      exact (tendsto_order.1 herror).2 _ hpos
    filter_upwards [hR_event, herr_event', happrox] with n hnR hnerr hnapprox
    dsimp [c] at hnerr
    linarith
  have hlower_le : lower ≤ Filter.liminf
      (fun n : ℕ => (prefixCount (Q ∩ K) n : ℝ) / (prefixCount K n : ℝ)) atTop := by
    refine Filter.le_liminf_of_le (hf := ratio_cobounded_above _ _ inter_subset_right) ?_
    exact hlower_event.mono fun _ h => h.le
  exact hblower.trans_le hlower_le

end Stage3Case025Formalization

open Stage3Case025
open Stage3Case025Formalization

 theorem stage3_finite_noise_transfer : FiniteNoiseTransferPrinciple := by
  intro hpositive
  intro family hfamily
  let expanded := finiteExtensionFamily family
  have hexpanded : ∀ n, (expanded n).Infinite := by
    intro n
    exact finiteExtensionFamily_infinite hfamily n
  rcases hpositive expanded hexpanded with ⟨gen, hgen⟩
  refine ⟨gen, ?_⟩
  intro i input hpresentation
  rcases presents_finite_extension hpresentation with ⟨code, hpresents⟩
  change GenLimit.Presents input (expanded code) at hpresents
  rcases hgen code input hpresents with ⟨output, hfollows, hnovel, hdensity⟩
  refine ⟨output, hfollows, ?_, ?_⟩
  · apply novel_transfer_of_finite_extension (R := expanded code)
    · rw [← hpresents]
      exact finite_bad_values hpresentation.2
    · exact hnovel
  · let Q : Set ℕ := GenLimit.GeneratorFirst input output
    have hKR : family i ⊆ expanded code := by
      intro x hx
      rw [← hpresents]
      exact hpresentation.1 hx
    have hfinite : (expanded code \ family i).Finite := by
      rw [← hpresents]
      exact finite_bad_values hpresentation.2
    exact hdensity.trans (finite_perturbation_relativeLowerDensity
      (Q := Q) (hfamily i) hKR hfinite)
