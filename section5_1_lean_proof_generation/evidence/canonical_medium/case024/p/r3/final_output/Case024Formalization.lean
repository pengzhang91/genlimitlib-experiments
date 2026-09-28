import Stage3Model
import Mathlib

open Filter MeasureTheory
open scoped Topology

namespace Case024

abbrev Language := Stage3Case024.Language
abbrev Stream := Stage3Case024.Stream

noncomputable def sparse : Language := Set.range (fun n : ℕ => 2 * n * n)

lemma sparse_infinite : sparse.Infinite := by
  apply Set.infinite_range_of_injective
  intro a b h
  exact Nat.mul_self_inj.mp (by simpa [mul_assoc] using h)

lemma sparse_compl_infinite : sparseᶜ.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro n
  refine ⟨2 * n + 1, ?_, by omega⟩
  simp only [Set.mem_compl_iff, Set.mem_range, sparse]
  rintro ⟨k, hk⟩
  apply Nat.not_even_bit1 n
  rw [← hk]
  simpa [mul_assoc] using even_two_mul (k * k)

noncomputable def equivOfInfiniteSets (A B : Set ℕ) (hA : A.Infinite) (hB : B.Infinite) : A ≃ B := by
  letI : Infinite A := hA.to_subtype
  letI : Infinite B := hB.to_subtype
  exact Classical.choice (inferInstance : Nonempty (A ≃ B))

noncomputable def commonEquiv : ℕ ≃ ℕ := by
  classical
  let e₀ := equivOfInfiniteSets sparse sparseᶜ sparse_infinite sparse_compl_infinite
  let e₁ := equivOfInfiniteSets sparseᶜ sparse sparse_compl_infinite sparse_infinite
  refine
    { toFun := fun n => if hn : n ∈ sparse then (e₀ ⟨n, hn⟩ : ℕ) else (e₁ ⟨n, hn⟩ : ℕ)
      invFun := fun n => if hn : n ∈ sparse then (e₁.symm ⟨n, hn⟩ : ℕ)
        else (e₀.symm ⟨n, hn⟩ : ℕ)
      left_inv := ?_
      right_inv := ?_ }
  · intro n
    by_cases hn : n ∈ sparse
    · have hm : (e₀ ⟨n, hn⟩ : ℕ) ∉ sparse := (e₀ ⟨n, hn⟩).property
      simp [hn, hm, e₀]
    · have hm : (e₁ ⟨n, hn⟩ : ℕ) ∈ sparse := (e₁ ⟨n, hn⟩).property
      simp [hn, hm, e₁]
  · intro n
    by_cases hn : n ∈ sparse
    · have hm : (e₁.symm ⟨n, hn⟩ : ℕ) ∉ sparse := (e₁.symm ⟨n, hn⟩).property
      simp [hn, hm, e₁]
    · have hm : (e₀.symm ⟨n, hn⟩ : ℕ) ∈ sparse := (e₀.symm ⟨n, hn⟩).property
      simp [hn, hm, e₀]

noncomputable def commonStream : Stream := commonEquiv

lemma commonStream_mem_iff (n : ℕ) : commonStream n ∈ sparse ↔ n ∉ sparse := by
  classical
  unfold commonStream commonEquiv
  dsimp
  by_cases hn : n ∈ sparse
  · simp only [hn, dite_true, not_true, iff_false]
    exact (equivOfInfiniteSets sparse sparseᶜ sparse_infinite
      sparse_compl_infinite ⟨n, hn⟩).property
  · simp only [hn, dite_false, not_false_eq_true, iff_true]
    exact (equivOfInfiniteSets sparseᶜ sparse sparse_compl_infinite
      sparse_infinite ⟨n, hn⟩).property

lemma commonStream_injective : Function.Injective commonStream := commonEquiv.injective

lemma commonStream_surjective : Function.Surjective commonStream := commonEquiv.surjective

lemma prefixCount_le (A B : Set ℕ) (h : A ⊆ B) (n : ℕ) :
    GenLimit.PatientScope.prefixCount A n ≤ GenLimit.PatientScope.prefixCount B n := by
  classical
  apply Finset.card_le_card
  intro x hx
  simp only [GenLimit.PatientScope.prefixFinset, Finset.mem_filter, Finset.mem_range] at hx ⊢
  exact ⟨hx.1, h hx.2⟩

lemma prefixCount_univ (n : ℕ) : GenLimit.PatientScope.prefixCount Set.univ n = n := by
  simp [GenLimit.PatientScope.prefixCount, GenLimit.PatientScope.prefixFinset]

lemma prefixCount_sparse_le (n : ℕ) :
    GenLimit.PatientScope.prefixCount sparse n ≤ Nat.sqrt n + 1 := by
  classical
  let F := GenLimit.PatientScope.prefixFinset sparse n
  let f : ℕ → ℕ := fun x => Nat.sqrt (x / 2)
  have hinj : Set.InjOn f (F : Set ℕ) := by
    intro a ha b hb he
    simp [F, GenLimit.PatientScope.prefixFinset] at ha hb
    obtain ⟨ka, rfl⟩ := ha.2
    obtain ⟨kb, rfl⟩ := hb.2
    have hk : ka = kb := by
      simpa [f, mul_assoc, Nat.sqrt_eq] using he
    subst kb
    rfl
  calc
    F.card = (F.image f).card := (Finset.card_image_iff.mpr hinj).symm
    _ ≤ (Finset.range (Nat.sqrt n + 1)).card := by
      apply Finset.card_le_card
      intro x hx
      simp only [Finset.mem_image, Finset.mem_range] at hx ⊢
      obtain ⟨a, ha, rfl⟩ := hx
      have ha' : a < n := (show a < n ∧ a ∈ sparse by
        simpa [F, GenLimit.PatientScope.prefixFinset] using ha).1
      exact Nat.lt_succ_of_le (Nat.sqrt_le_sqrt (Nat.div_le_self a 2 |>.trans ha'.le))
    _ = Nat.sqrt n + 1 := Finset.card_range _

lemma sqrt_ratio_tendsto : Tendsto (fun n : ℕ => ((Nat.sqrt n + 1 : ℕ) : ℝ) / n)
    atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt (show 0 < ε / 2 by positivity)
  refine ⟨(m + 1) ^ 2, fun n hn => ?_⟩
  have hms : m + 1 ≤ Nat.sqrt n := Nat.le_sqrt.mpr (by simpa [pow_two] using hn)
  have hspos : 0 < Nat.sqrt n := lt_of_lt_of_le (by omega) hms
  have hnpos : 0 < n := lt_of_lt_of_le (by positivity : 0 < (m + 1)^2) hn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)]
  have hfirst : ((Nat.sqrt n + 1 : ℕ) : ℝ) / n ≤ 2 / (Nat.sqrt n : ℝ) := by
    have hsone : (1 : ℝ) ≤ Nat.sqrt n := by exact_mod_cast hspos
    have hsquare : (Nat.sqrt n : ℝ) ^ 2 ≤ n := by
      norm_num [pow_two]
      exact_mod_cast (Nat.sqrt_le n)
    rw [div_le_iff₀ (by exact_mod_cast hnpos), div_eq_mul_inv]
    have hleft : ((Nat.sqrt n + 1 : ℕ) : ℝ) ≤ 2 * Nat.sqrt n := by
      push_cast
      linarith
    have hright : 2 * (Nat.sqrt n : ℝ) ≤ 2 * (Nat.sqrt n : ℝ)⁻¹ * n := by
      have hsposReal : (0 : ℝ) < Nat.sqrt n := by exact_mod_cast hspos
      rw [← div_eq_mul_inv, div_mul_eq_mul_div, le_div_iff₀ hsposReal]
      nlinarith
    exact hleft.trans hright
  have hsecond : 2 / (Nat.sqrt n : ℝ) ≤ 2 / (m + 1 : ℝ) := by
    gcongr
    exact_mod_cast hms
  have hthird : 2 / (m + 1 : ℝ) < ε := by
    have := hm
    norm_num [div_eq_mul_inv] at this ⊢
    linarith
  exact lt_of_le_of_lt (hfirst.trans hsecond) hthird

lemma sparse_ratio_tendsto : Tendsto
    (fun n : ℕ => (GenLimit.PatientScope.prefixCount sparse n : ℝ) / n)
    atTop (nhds 0) := by
  apply squeeze_zero'
  · filter_upwards with n
    positivity
  · filter_upwards with n
    have hc : (GenLimit.PatientScope.prefixCount sparse n : ℝ) ≤
        ((Nat.sqrt n + 1 : ℕ) : ℝ) := Nat.cast_le.mpr (prefixCount_sparse_le n)
    exact div_le_div_of_nonneg_right hc (by positivity)
  · exact sqrt_ratio_tendsto

-- Re-state the limit directly; this avoids depending on the preceding neighborhood witness.
lemma commonStream_noise_sparse :
    GenLimit.InfiniteContamination.VanishingNoise commonStream sparse := by
  unfold GenLimit.InfiniteContamination.VanishingNoise
  apply sparse_ratio_tendsto.congr'
  filter_upwards [eventually_ne_atTop 0] with n hn
  rw [GenLimit.InfiniteContamination.empiricalNoiseRate, if_neg hn]
  have hc : GenLimit.InfiniteContamination.noiseCount commonStream sparse n =
      GenLimit.PatientScope.prefixCount sparse n := by
    unfold GenLimit.InfiniteContamination.noiseCount
      GenLimit.PatientScope.prefixCount GenLimit.PatientScope.prefixFinset
    congr 1
    ext t
    simp [commonStream_mem_iff]
  rw [hc]

lemma legal_sparse : Stage3Case024.Legal commonStream sparse := by
  refine ⟨sparse_infinite, commonStream_injective, ?_, commonStream_noise_sparse⟩
  intro x hx
  exact commonStream_surjective x

lemma legal_univ : Stage3Case024.Legal commonStream Set.univ := by
  refine ⟨Set.infinite_univ, commonStream_injective, ?_, ?_⟩
  · intro x hx
    exact commonStream_surjective x
  · unfold GenLimit.InfiniteContamination.VanishingNoise
    convert (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0)) using 1
    funext n
    simp [GenLimit.InfiniteContamination.empiricalNoiseRate,
      GenLimit.InfiniteContamination.noiseCount]

lemma relativeUpperDensity_le_one (A K : Language) :
    Stage3Case024.relativeUpperDensity A K ≤ 1 := by
  unfold Stage3Case024.relativeUpperDensity
  apply Filter.limsup_le_of_le (hf :=
    Filter.isCoboundedUnder_le_of_le atTop (fun n => by positivity))
  filter_upwards with n
  by_cases h : GenLimit.PatientScope.prefixCount K n = 0
  · simp [h]
  · rw [div_le_one (by positivity)]
    exact_mod_cast prefixCount_le (A ∩ K) K Set.inter_subset_right n

lemma finite_exceptions_bound {output : Stream} {T : ℕ}
    (hvalid : ∀ t, T ≤ t → output t ∈ sparse) :
    Tendsto (fun n =>
      (GenLimit.PatientScope.prefixCount (Set.range output ∩ Set.univ) n : ℝ) / n)
      atTop (nhds 0) := by
  have hcard : ∀ n, GenLimit.PatientScope.prefixCount (Set.range output ∩ Set.univ) n ≤
      GenLimit.PatientScope.prefixCount sparse n + T := by
    intro n
    classical
    let F := GenLimit.PatientScope.prefixFinset (Set.range output ∩ Set.univ) n
    let early := F.filter (fun x => ∃ t < T, output t = x)
    let late := F.filter (fun x => ¬ ∃ t < T, output t = x)
    have hsplit : F.card ≤ early.card + late.card := by
      calc
        F.card = (early ∪ late).card := by
          congr 1
          ext x
          simp only [early, late, Finset.mem_union, Finset.mem_filter]
          constructor
          · intro hx
            by_cases h : ∃ t < T, output t = x
            · exact Or.inl ⟨hx, h⟩
            · exact Or.inr ⟨hx, h⟩
          · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
        _ ≤ early.card + late.card := Finset.card_union_le _ _
    have hearly : early.card ≤ T := by
      let g : Fin T → ℕ := fun t => output t
      calc
        early.card ≤ (Finset.univ.image g).card := by
          apply Finset.card_le_card
          intro x hx
          obtain ⟨hxF, t, ht, htx⟩ := Finset.mem_filter.mp hx
          exact Finset.mem_image.mpr ⟨⟨t, ht⟩, Finset.mem_univ _, htx⟩
        _ ≤ Finset.univ.card := Finset.card_image_le
        _ = T := Finset.card_fin T
    have hlate : late.card ≤ GenLimit.PatientScope.prefixCount sparse n := by
      apply Finset.card_le_card
      intro x hx
      have hxF := (Finset.mem_filter.mp hx).1
      have hxdata : x < n ∧ x ∈ Set.range output := by
        simpa [F, GenLimit.PatientScope.prefixFinset] using hxF
      obtain ⟨t, rfl⟩ := hxdata.2
      have hT : T ≤ t := by
        by_contra hnot
        exact (Finset.mem_filter.mp hx).2 ⟨t, Nat.lt_of_not_ge hnot, rfl⟩
      simp [GenLimit.PatientScope.prefixFinset, hxdata.1, hvalid t hT]
    change F.card ≤ GenLimit.PatientScope.prefixCount sparse n + T
    omega
  apply squeeze_zero'
  · filter_upwards with n
    positivity
  · filter_upwards with n
    calc
      (GenLimit.PatientScope.prefixCount (Set.range output ∩ Set.univ) n : ℝ) / n
          ≤ ((GenLimit.PatientScope.prefixCount sparse n + T : ℕ) : ℝ) / n := by
            refine div_le_div_of_nonneg_right ?_ (by positivity)
            exact_mod_cast hcard n
      _ = (GenLimit.PatientScope.prefixCount sparse n : ℝ) / n + (T : ℝ) / n := by
        push_cast
        ring
  · simpa using sparse_ratio_tendsto.add
      (tendsto_natCast_atTop_atTop.const_div_atTop (T : ℝ))

lemma generatorFirst_univ_zero {input output : Stream}
    (h : GenLimit.NovelGeneratesInLimit input output sparse) :
    Stage3Case024.relativeUpperDensity (GenLimit.GeneratorFirst input output) Set.univ = 0 := by
  obtain ⟨T, hT⟩ := h
  unfold Stage3Case024.relativeUpperDensity
  apply Filter.Tendsto.limsup_eq
  have hrange : GenLimit.GeneratorFirst input output ⊆ Set.range output := by
    intro x hx
    obtain ⟨t, rfl, _⟩ := hx
    exact ⟨t, rfl⟩
  have ht := finite_exceptions_bound (T := T) (fun t ht => (hT t ht).1)
  apply squeeze_zero'
  · filter_upwards with n
    positivity
  · filter_upwards [eventually_ge_atTop 1] with n hn
    simp only [prefixCount_univ]
    have hnat := prefixCount_le
      (GenLimit.GeneratorFirst input output ∩ Set.univ)
      (Set.range output ∩ Set.univ)
      (fun x hx => ⟨hrange hx.1, Set.mem_univ x⟩) n
    have hc : (GenLimit.PatientScope.prefixCount
        (GenLimit.GeneratorFirst input output ∩ Set.univ) n : ℝ) ≤
        (GenLimit.PatientScope.prefixCount (Set.range output ∩ Set.univ) n : ℝ) :=
      Nat.cast_le.mpr hnat
    exact div_le_div_of_nonneg_right hc (by positivity)
  · simpa [prefixCount_univ] using ht

lemma expected_univ_zero {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (input : Stream) (output : Ω → Stream)
    (h : Stage3Case024.EventuallyFreshValid μ sparse input output) :
    Stage3Case024.expectedUpperDensity μ Set.univ input output = 0 := by
  unfold Stage3Case024.expectedUpperDensity
  calc
    _ = ∫ _ : Ω, (0 : ℝ) ∂μ := integral_congr_ae (by
      filter_upwards [h] with ω hω
      exact generatorFirst_univ_zero hω)
    _ = 0 := by simp

lemma pair_obstruction : Stage3Case024.PairObstruction sparse Set.univ commonStream := by
  intro Ω _ μ _ gen output hfollows hmeas hi0 hi1 hv0 hv1
  have hz := expected_univ_zero μ commonStream output hv0
  have hle : Stage3Case024.expectedUpperDensity μ sparse commonStream output ≤ 1 := by
    unfold Stage3Case024.expectedUpperDensity
    calc
      _ ≤ ∫ _ : Ω, (1 : ℝ) ∂μ := integral_mono_ae hi0 (integrable_const 1) <|
        Filter.Eventually.of_forall fun ω => relativeUpperDensity_le_one _ _
      _ = 1 := by simp
  constructor
  · linarith
  · intro hbad
    linarith [hbad.2]

lemma odd_not_sparse (k : ℕ) : 2 * k + 1 ∉ sparse := by
  intro h
  obtain ⟨m, hm⟩ := h
  apply Nat.not_even_bit1 k
  rw [← hm]
  simpa [mul_assoc] using even_two_mul (m * m)

noncomputable def family (r : ℕ) (j : Fin r) : Language :=
  if (j : ℕ) = r - 1 then Set.univ
  else sparse ∪ {x | ∃ k < (j : ℕ), x = 2 * k + 1}

lemma sparse_subset_family (r : ℕ) (j : Fin r) : sparse ⊆ family r j := by
  intro x hx
  simp [family, hx]

lemma noiseCount_le_of_subset (K : Language) (hK : sparse ⊆ K) (n : ℕ) :
    GenLimit.InfiniteContamination.noiseCount commonStream K n ≤
      GenLimit.InfiniteContamination.noiseCount commonStream sparse n := by
  classical
  unfold GenLimit.InfiniteContamination.noiseCount
  apply Finset.card_le_card
  intro t ht
  simp only [Finset.mem_filter, Finset.mem_range] at ht ⊢
  exact ⟨ht.1, fun hs => ht.2 (hK hs)⟩

lemma legal_of_sparse_subset (K : Language) (hK : sparse ⊆ K) :
    Stage3Case024.Legal commonStream K := by
  refine ⟨sparse_infinite.mono hK, commonStream_injective, ?_, ?_⟩
  · intro x hx
    exact commonStream_surjective x
  · unfold GenLimit.InfiniteContamination.VanishingNoise
    apply squeeze_zero' (g :=
      GenLimit.InfiniteContamination.empiricalNoiseRate commonStream sparse)
    · filter_upwards with n
      unfold GenLimit.InfiniteContamination.empiricalNoiseRate
      positivity
    · filter_upwards with n
      unfold GenLimit.InfiniteContamination.empiricalNoiseRate
      by_cases hn : n = 0
      · simp [hn]
      · simp only [hn, if_false]
        refine div_le_div_of_nonneg_right ?_ (by positivity)
        exact Nat.cast_le.mpr (noiseCount_le_of_subset K hK n)
    · exact commonStream_noise_sparse

-- A choice generator selecting a fresh point of the common infinite core.
noncomputable def coreGen : Stage3Case024.OnlineGenerator := fun _ input output =>
  Classical.choose (sparse_infinite.exists_notMem_finset
    ((Finset.univ.image input) ∪ (Finset.univ.image output)))

lemma coreGen_mem_fresh (t : ℕ) (input : Fin (t+1) → ℕ) (output : Fin t → ℕ) :
    coreGen t input output ∈ sparse ∧
    coreGen t input output ∉ Set.range input ∧
    coreGen t input output ∉ Set.range output := by
  classical
  have h := Classical.choose_spec (sparse_infinite.exists_notMem_finset
    ((Finset.univ.image input) ∪ (Finset.univ.image output)))
  refine ⟨h.1, ?_, ?_⟩
  · intro hx
    obtain ⟨i, hi⟩ := hx
    exact h.2 (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩))
  · intro hx
    obtain ⟨i, hi⟩ := hx
    exact h.2 (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩))

noncomputable def followCore (input : Stream) (t : ℕ) : ℕ :=
  coreGen t (fun i => input i) (fun i => followCore input i)
termination_by t

lemma followCore_follows (input : Stream) : Stage3Case024.Follows coreGen input (followCore input) := by
  intro t
  rw [followCore]

lemma followCore_novel (input : Stream) : GenLimit.NovelGeneratesInLimit input (followCore input) sparse := by
  refine ⟨0, fun t _ => ?_⟩
  rw [followCore_follows input t]
  have h := coreGen_mem_fresh t (fun i => input i) (fun i => followCore input i)
  refine ⟨h.1, ?_, ?_⟩
  · intro hs
    simp only [GenLimit.sample, Finset.mem_image, Finset.mem_range] at hs
    obtain ⟨s, hs, heq⟩ := hs
    exact h.2.1 ⟨⟨s, hs⟩, heq⟩
  · intro s hs heq
    exact h.2.2 ⟨⟨s, hs⟩, heq⟩

lemma family_strict (r : ℕ) : Stage3Case024.StrictlyNested (family r) := by
  intro i j hij
  have hi : (i : ℕ) ≠ r - 1 := by omega
  by_cases hj : (j : ℕ) = r - 1
  · simp only [family, hi, hj, if_false, if_true]
    refine ⟨Set.subset_univ _, ?_⟩
    intro hsub
    have hmem := hsub (show 2 * (j : ℕ) + 1 ∈ Set.univ by simp)
    rcases hmem with hmem | ⟨k, hk, heq⟩
    · exact odd_not_sparse j hmem
    · omega
  · simp only [family, hi, hj, if_false]
    refine ⟨?_, ?_⟩
    · intro x hx
      rcases hx with hx | ⟨k, hk, rfl⟩
      · exact Or.inl hx
      · exact Or.inr ⟨k, lt_trans hk hij, rfl⟩
    · intro hsub
      have hmem := hsub (show 2 * (i : ℕ) + 1 ∈
        sparse ∪ {x | ∃ k < (j : ℕ), x = 2 * k + 1} by
          exact Or.inr ⟨i, hij, rfl⟩)
      rcases hmem with hmem | ⟨k, hk, heq⟩
      · exact odd_not_sparse i hmem
      · omega

lemma family_witness (r : ℕ) (hr : 2 ≤ r) :
    ∃ f : Fin r → Language, ∃ input : Stream, Stage3Case024.ManyTargetWitness f input := by
  refine ⟨family r, commonStream, family_strict r, ?_, ?_, ?_⟩
  · intro j
    exact legal_of_sparse_subset _ (sparse_subset_family r j)
  · refine ⟨coreGen, fun input _ => ⟨followCore input, followCore_follows input, ?_⟩⟩
    intro j
    obtain ⟨T, hT⟩ := followCore_novel input
    exact ⟨T, fun t ht => ⟨sparse_subset_family r j (hT t ht).1, (hT t ht).2⟩⟩
  · intro Ω _ μ _ gen output hf hm hi hv
    let last : Fin r := ⟨r - 1, by omega⟩
    refine ⟨last, ?_⟩
    have hfamily0 : family r (⟨0, by omega⟩ : Fin r) = sparse := by
      simp [family]
      omega
    have hv0 := hv (⟨0, by omega⟩ : Fin r)
    rw [hfamily0] at hv0
    have hzero := expected_univ_zero μ commonStream output hv0
    have hlast : family r last = Set.univ := by
      simp [family, last]
    rw [hlast]
    exact hzero

end Case024

open Case024

theorem stage3_result : Stage3Case024.MainClaim := by
  constructor
  · refine ⟨sparse, Set.univ, commonStream, ?_, legal_sparse, legal_univ, pair_obstruction⟩
    refine ⟨Set.subset_univ _, ?_⟩
    intro hsub
    exact odd_not_sparse 0 (hsub (by simp))
  · exact family_witness
