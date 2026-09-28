import Stage3Model

open Filter
open scoped Topology

namespace Stage3Case025

noncomputable def expandedFamily (family : ℕ → Language) (n : ℕ) : Language :=
  match Encodable.decode (α := ℕ × List ℕ) n with
  | some p => family p.1 ∪ (p.2.toFinset : Set ℕ)
  | none => family 0

lemma expandedFamily_infinite (family : ℕ → Language)
    (hfamily : ∀ i, (family i).Infinite) :
    ∀ n, (expandedFamily family n).Infinite := by
  intro n
  unfold expandedFamily
  split
  · rename_i p hp
    exact (hfamily p.1).mono Set.subset_union_left
  · exact hfamily 0

lemma expandedFamily_encode (family : ℕ → Language) (i : ℕ) (F : Finset ℕ) :
    expandedFamily family (Encodable.encode (i, F.toList)) = family i ∪ (F : Set ℕ) := by
  simp [expandedFamily]

noncomputable def badValueFinset (input : Stream) (K : Language)
    (hbad : GenLimit.Generic.FinitelyManyViolations input (fun x => x ∈ K)) : Finset ℕ :=
  hbad.toFinset.image input

lemma presents_expanded_of_complete
    (input : Stream) (K : Language)
    (h : CompleteFiniteOccurrencePresentation input K) :
    GenLimit.Presents input (K ∪ (badValueFinset input K h.2 : Set ℕ)) := by
  rcases h with ⟨hcover, hbad⟩
  apply Set.Subset.antisymm
  · rintro x ⟨t, rfl⟩
    by_cases hx : input t ∈ K
    · exact Set.mem_union_left _ hx
    · apply Set.mem_union_right
      simp only [badValueFinset, Finset.mem_coe, Finset.mem_image]
      exact ⟨t, by simpa [GenLimit.Generic.ViolationIndices] using hx, rfl⟩
  · intro x hx
    rcases hx with hx | hx
    · exact hcover hx
    · simp only [badValueFinset, Finset.mem_coe, Finset.mem_image] at hx
      rcases hx with ⟨t, ht, rfl⟩
      exact ⟨t, rfl⟩

lemma tail_injective_of_novel
    {input output : Stream} {K : Language} {T : ℕ}
    (h : ∀ t, T ≤ t →
      output t ∈ K ∧ output t ∉ GenLimit.sample input (t + 1) ∧
        ∀ s, s < t → output s ≠ output t) :
    Set.InjOn output {t | T ≤ t} := by
  intro a ha b hb hab
  rcases lt_trichotomy a b with hablt | rfl | hbalt
  · exact False.elim ((h b hb).2.2 a hablt hab)
  · rfl
  · exact False.elim ((h a ha).2.2 b hbalt hab.symm)

lemma eventually_avoid_finset_of_novel
    {input output : Stream} {K : Language} {T : ℕ}
    (h : ∀ t, T ≤ t →
      output t ∈ K ∧ output t ∉ GenLimit.sample input (t + 1) ∧
        ∀ s, s < t → output s ≠ output t)
    (F : Finset ℕ) :
    ∃ T', ∀ t, T' ≤ t → output t ∉ F := by
  let badTimes : Set ℕ := {t | T ≤ t ∧ output t ∈ F}
  have hfinite : badTimes.Finite := by
    apply Set.Finite.of_finite_image (f := output)
    · apply F.finite_toSet.subset
      rintro x ⟨t, ht, rfl⟩
      exact ht.2
    · intro a ha b hb hab
      exact tail_injective_of_novel h ha.1 hb.1 hab
  rcases hfinite.bddAbove with ⟨bound, hbound⟩
  refine ⟨max T (bound + 1), ?_⟩
  intro t htt hmem
  have htT : T ≤ t := (le_max_left T (bound + 1)).trans htt
  have htle : t ≤ bound := hbound ⟨htT, hmem⟩
  have hsucc : bound + 1 ≤ t := (le_max_right T (bound + 1)).trans htt
  omega

end Stage3Case025

namespace Stage3Case025

lemma prefixCount_eq_indicator (S : Set ℕ) (n : ℕ) :
    GenLimit.PatientScope.prefixCount S n =
      ∑ k ∈ Finset.range n, S.indicator (fun _ => 1) k := by
  classical
  unfold GenLimit.PatientScope.prefixCount GenLimit.PatientScope.prefixFinset
  rw [Finset.card_filter]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hmem : k ∈ S <;> simp [hmem]

lemma prefixCount_tendsto_atTop {K : Set ℕ} (hK : K.Infinite) :
    Tendsto (GenLimit.PatientScope.prefixCount K) atTop atTop := by
  rw [show GenLimit.PatientScope.prefixCount K =
    fun n => ∑ k ∈ Finset.range n, K.indicator (fun _ => 1) k from by
      funext n
      exact prefixCount_eq_indicator K n]
  exact (Set.infinite_iff_tendsto_sum_indicator_atTop (R := ℕ) Nat.zero_lt_one).mp hK

lemma prefixCount_mono {A B : Set ℕ} (hAB : A ⊆ B) (n : ℕ) :
    GenLimit.PatientScope.prefixCount A n ≤ GenLimit.PatientScope.prefixCount B n := by
  classical
  apply Finset.card_le_card
  intro x hx
  simp only [GenLimit.PatientScope.prefixFinset, Finset.mem_filter, Finset.mem_range] at hx ⊢
  exact ⟨hx.1, hAB hx.2⟩

lemma prefixCount_union_le (A : Set ℕ) (F : Finset ℕ) (n : ℕ) :
    GenLimit.PatientScope.prefixCount (A ∪ (F : Set ℕ)) n ≤
      GenLimit.PatientScope.prefixCount A n + F.card := by
  classical
  let a := GenLimit.PatientScope.prefixFinset A n
  let f := (Finset.range n).filter (fun x => x ∈ F)
  have heq : GenLimit.PatientScope.prefixFinset (A ∪ (F : Set ℕ)) n = a ∪ f := by
    ext x
    simp only [a, f, GenLimit.PatientScope.prefixFinset, Finset.mem_filter,
      Finset.mem_range, Set.mem_union, Finset.mem_union]
    tauto
  rw [GenLimit.PatientScope.prefixCount, heq]
  exact (Finset.card_union_le a f).trans (Nat.add_le_add_left (Finset.card_le_card (by
    intro x hx
    simp only [f, Finset.mem_filter] at hx
    exact hx.2)) _)

lemma ratio_nonneg (A K : Set ℕ) (n : ℕ) :
    0 ≤ (GenLimit.PatientScope.prefixCount A n : ℝ) /
      (GenLimit.PatientScope.prefixCount K n : ℝ) := by positivity

end Stage3Case025

namespace Stage3Case025

private noncomputable def densityRatio (A K : Set ℕ) (n : ℕ) : ℝ :=
  (GenLimit.PatientScope.prefixCount A n : ℝ) /
    (GenLimit.PatientScope.prefixCount K n : ℝ)

lemma densityRatio_finite_perturbation_le
    {A A' K : Set ℕ} (F : Finset ℕ) (hA : A' ⊆ A ∪ (F : Set ℕ))
    (n : ℕ) (hKpos : 0 < GenLimit.PatientScope.prefixCount K n) :
    densityRatio A' (K ∪ (F : Set ℕ)) n ≤
      densityRatio A K n + (F.card : ℝ) /
        (GenLimit.PatientScope.prefixCount K n : ℝ) := by
  have hnumNat : GenLimit.PatientScope.prefixCount A' n ≤
      GenLimit.PatientScope.prefixCount A n + F.card :=
    (prefixCount_mono hA n).trans (prefixCount_union_le A F n)
  have hdenNat : GenLimit.PatientScope.prefixCount K n ≤
      GenLimit.PatientScope.prefixCount (K ∪ (F : Set ℕ)) n :=
    prefixCount_mono Set.subset_union_left n
  have hnum : (GenLimit.PatientScope.prefixCount A' n : ℝ) ≤
      (GenLimit.PatientScope.prefixCount A n : ℝ) + F.card := by exact_mod_cast hnumNat
  have hden : (GenLimit.PatientScope.prefixCount K n : ℝ) ≤
      GenLimit.PatientScope.prefixCount (K ∪ (F : Set ℕ)) n := by exact_mod_cast hdenNat
  have hk : (0 : ℝ) < GenLimit.PatientScope.prefixCount K n := by exact_mod_cast hKpos
  have hku : (0 : ℝ) < GenLimit.PatientScope.prefixCount (K ∪ (F : Set ℕ)) n :=
    hk.trans_le hden
  unfold densityRatio
  calc
    (GenLimit.PatientScope.prefixCount A' n : ℝ) /
        GenLimit.PatientScope.prefixCount (K ∪ (F : Set ℕ)) n
      ≤ ((GenLimit.PatientScope.prefixCount A n : ℝ) + F.card) /
          GenLimit.PatientScope.prefixCount (K ∪ (F : Set ℕ)) n := by
            exact div_le_div_of_nonneg_right hnum hku.le
    _ ≤ ((GenLimit.PatientScope.prefixCount A n : ℝ) + F.card) /
          GenLimit.PatientScope.prefixCount K n := by
            exact div_le_div_of_nonneg_left (by positivity) hk hden
    _ = (GenLimit.PatientScope.prefixCount A n : ℝ) /
          GenLimit.PatientScope.prefixCount K n +
          (F.card : ℝ) / GenLimit.PatientScope.prefixCount K n := by
            rw [add_div]

lemma relativeLowerDensity_finite_perturbation
    {A A' K : Set ℕ} (F : Finset ℕ) (hK : K.Infinite)
    (hAK : A ⊆ K) (hA : A' ⊆ A ∪ (F : Set ℕ))
    (hhalf : (1 / 2 : ℝ) ≤
      GenLimit.PatientScope.relativeLowerDensity A' (K ∪ (F : Set ℕ))) :
    (1 / 2 : ℝ) ≤ GenLimit.PatientScope.relativeLowerDensity A K := by
  unfold GenLimit.PatientScope.relativeLowerDensity
  change (1 / 2 : ℝ) ≤ liminf (densityRatio A K) atTop
  apply le_of_forall_lt
  intro b hb
  let mid : ℝ := (b + (1 / 2 : ℝ)) / 2
  have hbmid : b < mid := by dsimp [mid]; linarith
  have hmidhalf : mid < (1 / 2 : ℝ) := by dsimp [mid]; linarith
  let low : ℝ := (b + mid) / 2
  have hblow : b < low := by dsimp [low]; linarith
  have hlowmid : low < mid := by dsimp [low]; linarith
  have hmidlim : mid < liminf (densityRatio A' (K ∪ (F : Set ℕ))) atTop :=
    hmidhalf.trans_le hhalf
  have hnonneg : ∀ᶠ n in atTop, 0 ≤ densityRatio A' (K ∪ (F : Set ℕ)) n :=
    Filter.Eventually.of_forall (fun n => ratio_nonneg _ _ n)
  have hlarge := eventually_lt_of_lt_liminf hmidlim
    (isBoundedUnder_of_eventually_ge hnonneg)
  have hcountNat := prefixCount_tendsto_atTop hK
  have hcountReal : Tendsto
      (fun n => (GenLimit.PatientScope.prefixCount K n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_iff.mpr hcountNat
  have herr : Tendsto
      (fun n => (F.card : ℝ) / (GenLimit.PatientScope.prefixCount K n : ℝ))
      atTop (𝓝 0) := hcountReal.const_div_atTop F.card
  have heps : 0 < mid - low := sub_pos.mpr hlowmid
  have herrSmall : ∀ᶠ n in atTop,
      (F.card : ℝ) / (GenLimit.PatientScope.prefixCount K n : ℝ) < mid - low := by
    have := (tendsto_order.1 herr).2 (mid - low) heps
    simpa using this
  have hpos : ∀ᶠ n in atTop, 0 < GenLimit.PatientScope.prefixCount K n := by
    filter_upwards [hcountNat.eventually (eventually_ge_atTop 1)] with n hn
    omega
  have hpoint : ∀ᶠ n in atTop, low ≤ densityRatio A K n := by
    filter_upwards [hlarge, herrSmall, hpos] with n hn herror hnpos
    have hpert := densityRatio_finite_perturbation_le F hA n hnpos
    linarith
  have hratio_le : ∀ n, densityRatio A K n ≤ 1 := by
    intro n
    unfold densityRatio
    have hcount := prefixCount_mono hAK n
    by_cases hzero : GenLimit.PatientScope.prefixCount K n = 0
    · simp [hzero]
    · apply (div_le_one (by positivity)).2
      exact_mod_cast hcount
  have hlowlim : low ≤ liminf (densityRatio A K) atTop :=
    le_liminf_of_le (isCoboundedUnder_ge_of_le atTop hratio_le) hpoint
  exact hblow.trans_le hlowlim

end Stage3Case025
