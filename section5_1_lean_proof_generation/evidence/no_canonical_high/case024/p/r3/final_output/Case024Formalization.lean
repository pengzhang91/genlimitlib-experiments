import Stage3Model
import Mathlib

open Filter MeasureTheory
open scoped Topology

namespace Case024

noncomputable section

def sparse : Set ℕ := Set.range (fun k : ℕ => 2 ^ k)

lemma sparse_infinite : sparse.Infinite := by
  exact Set.infinite_range_of_injective (fun _ _ h => Nat.pow_right_injective (by omega) h)

lemma sparse_compl_infinite : (Set.compl sparse).Infinite := by
  apply Set.infinite_of_injective_forall_mem (f := fun k : ℕ => 3 * k + 3)
  · intro a b h
    have h' := Nat.add_right_cancel h
    omega
  · intro k
    change 3 * k + 3 ∉ sparse
    intro hk
    rcases hk with ⟨n, hn⟩
    change 2 ^ n = 3 * k + 3 at hn
    have hdiv : 3 ∣ 2 ^ n := by
      rw [hn]
      use k + 1
      omega
    have : 3 ∣ 2 := Nat.prime_three.dvd_of_dvd_pow hdiv
    norm_num at this

noncomputable def sparseEquivCompl : sparse ≃ Set.compl sparse := by
  classical
  letI : Denumerable sparse := Classical.choice
    (Set.countable_infinite_iff_nonempty_denumerable.mp
      ⟨Set.countable_range _, sparse_infinite⟩)
  letI : Denumerable (Set.compl sparse) := Classical.choice
    (Set.countable_infinite_iff_nonempty_denumerable.mp
      ⟨Set.to_countable _, sparse_compl_infinite⟩)
  exact (Denumerable.eqv sparse).trans (Denumerable.eqv (Set.compl sparse)).symm

noncomputable def swapFun (n : ℕ) : ℕ := by
  classical
  exact if hn : n ∈ sparse then sparseEquivCompl ⟨n, hn⟩
    else sparseEquivCompl.symm ⟨n, hn⟩

lemma swapFun_involutive : Function.Involutive swapFun := by
  intro n
  classical
  by_cases hn : n ∈ sparse
  · have hout : (sparseEquivCompl ⟨n, hn⟩ : ℕ) ∉ sparse :=
      (sparseEquivCompl ⟨n, hn⟩).property
    rw [show swapFun n = (sparseEquivCompl ⟨n, hn⟩ : ℕ) by simp [swapFun, hn]]
    change swapFun (sparseEquivCompl ⟨n, hn⟩ : ℕ) = n
    unfold swapFun
    rw [dif_neg hout]
    simpa using congrArg Subtype.val (sparseEquivCompl.symm_apply_apply ⟨n, hn⟩)
  · have hout : (sparseEquivCompl.symm ⟨n, hn⟩ : ℕ) ∈ sparse :=
      (sparseEquivCompl.symm ⟨n, hn⟩).property
    rw [show swapFun n = (sparseEquivCompl.symm ⟨n, hn⟩ : ℕ) by simp [swapFun, hn]]
    change swapFun (sparseEquivCompl.symm ⟨n, hn⟩ : ℕ) = n
    unfold swapFun
    rw [dif_pos hout]
    simpa using congrArg Subtype.val (sparseEquivCompl.apply_symm_apply ⟨n, hn⟩)

noncomputable def swapPerm : ℕ ≃ ℕ := swapFun_involutive.toPerm swapFun

lemma swapPerm_mem_sparse_iff (n : ℕ) : swapPerm n ∈ sparse ↔ n ∉ sparse := by
  classical
  by_cases hn : n ∈ sparse
  · simp [swapPerm, swapFun, hn]
    exact (sparseEquivCompl ⟨n, hn⟩).property
  · simp [swapPerm, swapFun, hn]

lemma swapPerm_not_mem_sparse_iff (n : ℕ) : swapPerm n ∉ sparse ↔ n ∈ sparse := by
  rw [not_congr (swapPerm_mem_sparse_iff n), not_not]

lemma prefixCount_sparse_le (n : ℕ) :
    GenLimit.PatientScope.prefixCount sparse n ≤ Nat.log2 n + 1 := by
  classical
  unfold GenLimit.PatientScope.prefixCount GenLimit.PatientScope.prefixFinset
  calc
    ((Finset.range n).filter fun x => x ∈ sparse).card ≤
        ((Finset.range (Nat.log2 n + 1)).image fun k => 2 ^ k).card := by
          apply Finset.card_le_card
          intro x hx
          simp only [Finset.mem_filter, Finset.mem_range] at hx
          rcases hx.2 with ⟨k, rfl⟩
          simp only [Finset.mem_image, Finset.mem_range]
          refine ⟨k, ?_, rfl⟩
          have hn : n ≠ 0 := by
            intro hn
            subst n
            omega
          have hk : k ≤ Nat.log2 n := (Nat.le_log2 hn).2 (Nat.le_of_lt hx.1)
          omega
    _ ≤ (Finset.range (Nat.log2 n + 1)).card := Finset.card_image_le
    _ = Nat.log2 n + 1 := Finset.card_range _

lemma tendsto_log2_add_one_div :
    Tendsto (fun n : ℕ => ((Nat.log2 n + 1 : ℕ) : ℝ) / n) atTop (nhds 0) := by
  have hlog : Tendsto (fun n : ℕ => Real.logb 2 (n : ℝ) / (n : ℝ)) atTop (nhds 0) := by
    simpa only [id_eq] using
      (Real.isLittleO_logb_id_atTop (b := 2)).natCast_atTop.tendsto_div_nhds_zero
  have hone : Tendsto (fun n : ℕ => (1 : ℝ) / n) atTop (nhds 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall (fun n => div_nonneg (by positivity) (by positivity))
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hcast : (Nat.log2 n : ℝ) ≤ Real.logb 2 (n : ℝ) := Real.log2_le_logb n
    calc
      (((Nat.log2 n + 1 : ℕ) : ℝ) / n) =
          (Nat.log2 n : ℝ) / n + (1 : ℝ) / n := by push_cast; ring
      _ ≤ Real.logb 2 (n : ℝ) / n + (1 : ℝ) / n := by gcongr
  · simpa using hlog.add hone

lemma sparse_rate_zero :
    Tendsto (fun n : ℕ =>
      (GenLimit.PatientScope.prefixCount sparse n : ℝ) / n) atTop (nhds 0) := by
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall (fun n => div_nonneg (by positivity) (by positivity))
  · exact Filter.Eventually.of_forall (fun n => by
      have hcast : (GenLimit.PatientScope.prefixCount sparse n : ℝ) ≤
          ((Nat.log2 n + 1 : ℕ) : ℝ) := by exact_mod_cast prefixCount_sparse_le n
      exact div_le_div_of_nonneg_right hcast (by positivity))
  · exact tendsto_log2_add_one_div

lemma swapPerm_vanishing_sparse :
    GenLimit.InfiniteContamination.VanishingNoise swapPerm sparse := by
  unfold GenLimit.InfiniteContamination.VanishingNoise
  have hcount : ∀ n,
      GenLimit.InfiniteContamination.noiseCount swapPerm sparse n =
        GenLimit.PatientScope.prefixCount sparse n := by
    intro n
    classical
    unfold GenLimit.InfiniteContamination.noiseCount
    unfold GenLimit.PatientScope.prefixCount GenLimit.PatientScope.prefixFinset
    congr 1
    ext t
    simp [swapPerm_not_mem_sparse_iff]
  refine sparse_rate_zero.congr' ?_
  filter_upwards [eventually_ne_atTop 0] with n hn
  simp [GenLimit.InfiniteContamination.empiricalNoiseRate, hcount, hn]

lemma swapPerm_legal_sparse : Stage3Case024.Legal swapPerm sparse := by
  refine ⟨sparse_infinite, swapPerm.injective, ?_, swapPerm_vanishing_sparse⟩
  intro x hx
  exact swapPerm.surjective x


lemma prefixCount_mono {A B : Set ℕ} (h : A ⊆ B) (n : ℕ) :
    GenLimit.PatientScope.prefixCount A n ≤
      GenLimit.PatientScope.prefixCount B n := by
  classical
  unfold GenLimit.PatientScope.prefixCount GenLimit.PatientScope.prefixFinset
  apply Finset.card_le_card
  intro x hx
  simp only [Finset.mem_filter, Finset.mem_range] at hx ⊢
  exact ⟨hx.1, h hx.2⟩

lemma prefixCount_univ (n : ℕ) :
    GenLimit.PatientScope.prefixCount (Set.univ : Set ℕ) n = n := by
  classical
  simp [GenLimit.PatientScope.prefixCount, GenLimit.PatientScope.prefixFinset]

lemma relativeUpperDensity_le_one (A K : Set ℕ) :
    Stage3Case024.relativeUpperDensity A K ≤ 1 := by
  unfold Stage3Case024.relativeUpperDensity
  calc
    limsup (fun n : ℕ =>
      (GenLimit.PatientScope.prefixCount (A ∩ K) n : ℝ) /
        (GenLimit.PatientScope.prefixCount K n : ℝ)) atTop ≤
        limsup (fun _ : ℕ => (1 : ℝ)) atTop := by
          refine limsup_le_limsup (Filter.Eventually.of_forall (fun n => ?_))
            (isCoboundedUnder_le_of_le atTop (fun n => div_nonneg (by positivity) (by positivity)))
            (isBoundedUnder_of ⟨1, fun _ => le_rfl⟩)
          have hcount := prefixCount_mono (A := A ∩ K) (B := K) Set.inter_subset_right n
          by_cases hz : GenLimit.PatientScope.prefixCount K n = 0
          · simp [hz]
          · exact (div_le_one (by positivity)).2 (by exact_mod_cast hcount)
    _ = 1 := limsup_const 1

lemma generatorFirst_subset_sparse_union_early
    {input output : ℕ → ℕ}
    (h : GenLimit.NovelGeneratesInLimit input output sparse) :
    ∃ T, GenLimit.GeneratorFirst input output ⊆
      sparse ∪ Set.range (fun i : Fin T => output i) := by
  rcases h with ⟨T, hT⟩
  refine ⟨T, ?_⟩
  intro x hx
  rcases hx with ⟨t, hout, hfirst⟩
  by_cases ht : T ≤ t
  · left
    rw [← hout]
    exact (hT t ht).1
  · right
    exact ⟨⟨t, Nat.lt_of_not_ge ht⟩, hout⟩

lemma prefixCount_le_sparse_add_early
    {A : Set ℕ} {output : ℕ → ℕ} {T : ℕ}
    (h : A ⊆ sparse ∪ Set.range (fun i : Fin T => output i)) (n : ℕ) :
    GenLimit.PatientScope.prefixCount A n ≤
      GenLimit.PatientScope.prefixCount sparse n + T := by
  classical
  unfold GenLimit.PatientScope.prefixCount GenLimit.PatientScope.prefixFinset
  let early : Finset ℕ := Finset.univ.image (fun i : Fin T => output i)
  calc
    ((Finset.range n).filter fun x => x ∈ A).card ≤
        (((Finset.range n).filter fun x => x ∈ sparse) ∪ early).card := by
          apply Finset.card_le_card
          intro x hx
          simp only [Finset.mem_filter, Finset.mem_range] at hx
          have hx' := h hx.2
          rcases hx' with hs | he
          · exact Finset.mem_union_left _ (by simpa using ⟨hx.1, hs⟩)
          · apply Finset.mem_union_right
            rcases he with ⟨i, rfl⟩
            simp [early]
    _ ≤ ((Finset.range n).filter fun x => x ∈ sparse).card + early.card :=
      Finset.card_union_le _ _
    _ ≤ ((Finset.range n).filter fun x => x ∈ sparse).card + T := by
      gcongr
      simpa [early] using (Finset.card_image_le (s := Finset.univ) (f := fun i : Fin T => output i))

lemma tendsto_sparse_add_const_div (T : ℕ) :
    Tendsto (fun n : ℕ =>
      ((GenLimit.PatientScope.prefixCount sparse n + T : ℕ) : ℝ) / n)
      atTop (nhds 0) := by
  have hT : Tendsto (fun n : ℕ => (T : ℝ) / n) atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using
      tendsto_one_div_atTop_nhds_zero_nat.const_mul (T : ℝ)
  simpa only [Nat.cast_add, add_div, zero_add] using sparse_rate_zero.add hT

lemma relativeUpperDensity_generatorFirst_univ_zero
    {input output : ℕ → ℕ}
    (h : GenLimit.NovelGeneratesInLimit input output sparse) :
    Stage3Case024.relativeUpperDensity
      (GenLimit.GeneratorFirst input output) Set.univ = 0 := by
  rcases generatorFirst_subset_sparse_union_early h with ⟨T, hsub⟩
  unfold Stage3Case024.relativeUpperDensity
  have htend : Tendsto (fun n : ℕ =>
      (GenLimit.PatientScope.prefixCount
        (GenLimit.GeneratorFirst input output) n : ℝ) / n) atTop (nhds 0) := by
    apply squeeze_zero'
    · exact Filter.Eventually.of_forall (fun n => div_nonneg (by positivity) (by positivity))
    · exact Filter.Eventually.of_forall (fun n => by
        have hc := prefixCount_le_sparse_add_early hsub n
        have hcast : (GenLimit.PatientScope.prefixCount
            (GenLimit.GeneratorFirst input output) n : ℝ) ≤
            ((GenLimit.PatientScope.prefixCount sparse n + T : ℕ) : ℝ) := by
          exact_mod_cast hc
        exact div_le_div_of_nonneg_right hcast (by positivity))
    · exact tendsto_sparse_add_const_div T
  have heq : (fun n : ℕ =>
      (GenLimit.PatientScope.prefixCount
        (GenLimit.GeneratorFirst input output ∩ Set.univ) n : ℝ) /
        (GenLimit.PatientScope.prefixCount (Set.univ : Set ℕ) n : ℝ)) =
      fun n : ℕ =>
        (GenLimit.PatientScope.prefixCount
          (GenLimit.GeneratorFirst input output) n : ℝ) / n := by
    funext n
    rw [Set.inter_univ, prefixCount_univ]
  rw [heq]
  exact htend.limsup_eq


lemma special_injective : Function.Injective (fun k : ℕ => 3 * k + 3) := by
  intro a b h
  have h' := Nat.add_right_cancel h
  omega

lemma special_not_mem_sparse (k : ℕ) : 3 * k + 3 ∉ sparse := by
  intro hk
  rcases hk with ⟨n, hn⟩
  change 2 ^ n = 3 * k + 3 at hn
  have hdiv : 3 ∣ 2 ^ n := by
    rw [hn]
    use k + 1
    omega
  have : 3 ∣ 2 := Nat.prime_three.dvd_of_dvd_pow hdiv
  norm_num at this

lemma noiseCount_le_sparse (K : Set ℕ) (hsub : sparse ⊆ K) (n : ℕ) :
    GenLimit.InfiniteContamination.noiseCount swapPerm K n ≤
      GenLimit.PatientScope.prefixCount sparse n := by
  classical
  unfold GenLimit.InfiniteContamination.noiseCount
  unfold GenLimit.PatientScope.prefixCount GenLimit.PatientScope.prefixFinset
  apply Finset.card_le_card
  intro t ht
  simp only [Finset.mem_filter, Finset.mem_range] at ht ⊢
  refine ⟨ht.1, ?_⟩
  rw [← swapPerm_not_mem_sparse_iff]
  exact fun hs => ht.2 (hsub hs)

lemma swapPerm_vanishing_of_sparse_subset (K : Set ℕ) (hsub : sparse ⊆ K) :
    GenLimit.InfiniteContamination.VanishingNoise swapPerm K := by
  unfold GenLimit.InfiniteContamination.VanishingNoise
  have htend : Tendsto (fun n : ℕ =>
      (GenLimit.InfiniteContamination.noiseCount swapPerm K n : ℝ) / n)
      atTop (nhds 0) := by
    apply squeeze_zero'
    · exact Filter.Eventually.of_forall (fun n => div_nonneg (by positivity) (by positivity))
    · exact Filter.Eventually.of_forall (fun n => by
        have hc := noiseCount_le_sparse K hsub n
        have hcast : (GenLimit.InfiniteContamination.noiseCount swapPerm K n : ℝ) ≤
            (GenLimit.PatientScope.prefixCount sparse n : ℝ) := by exact_mod_cast hc
        exact div_le_div_of_nonneg_right hcast (by positivity))
    · exact sparse_rate_zero
  refine htend.congr' ?_
  filter_upwards [eventually_ne_atTop 0] with n hn
  simp [GenLimit.InfiniteContamination.empiricalNoiseRate, hn]

lemma swapPerm_legal_of_sparse_subset (K : Set ℕ) (hsub : sparse ⊆ K) :
    Stage3Case024.Legal swapPerm K := by
  refine ⟨sparse_infinite.mono hsub, swapPerm.injective, ?_,
    swapPerm_vanishing_of_sparse_subset K hsub⟩
  intro x hx
  exact swapPerm.surjective x

lemma swapPerm_legal_univ : Stage3Case024.Legal swapPerm Set.univ :=
  swapPerm_legal_of_sparse_subset Set.univ (fun _ _ => trivial)

noncomputable def family (r : ℕ) (j : Fin r) : Set ℕ :=
  if j.val + 1 = r then Set.univ
  else sparse ∪ Set.range (fun k : Fin j.val => 3 * k.val + 3)

lemma family_zero {r : ℕ} (hr : 2 ≤ r) : family r ⟨0, by omega⟩ = sparse := by
  simp [family, show 0 + 1 ≠ r by omega]

lemma family_last {r : ℕ} (hr : 2 ≤ r) :
    family r ⟨r - 1, by omega⟩ = Set.univ := by
  simp [family, show r - 1 + 1 = r by omega]

lemma sparse_subset_family {r : ℕ} (j : Fin r) : sparse ⊆ family r j := by
  classical
  unfold family
  split
  · exact Set.subset_univ _
  · exact Set.subset_union_left

lemma family_strictlyNested {r : ℕ} (hr : 2 ≤ r) :
    Stage3Case024.StrictlyNested (family r) := by
  intro i j hij
  classical
  have hi_not_last : i.val + 1 ≠ r := by omega
  by_cases hj_last : j.val + 1 = r
  · simp only [family, hi_not_last, hj_last, if_false, if_true]
    refine Set.ssubset_iff_subset_ne.mpr ⟨Set.subset_univ _, ?_⟩
    intro heq
    have hw : 3 * r + 3 ∈ sparse ∪ Set.range (fun k : Fin i.val => 3 * k.val + 3) := by
      rw [heq]
      trivial
    rcases hw with hs | he
    · exact special_not_mem_sparse r hs
    · rcases he with ⟨k, hk⟩
      have := special_injective hk
      omega
  · simp only [family, hi_not_last, hj_last, if_false]
    refine Set.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
    · intro x hx
      rcases hx with hs | he
      · exact Or.inl hs
      · right
        rcases he with ⟨k, rfl⟩
        exact ⟨⟨k.val, by omega⟩, rfl⟩
    · intro heq
      have hwj : 3 * i.val + 3 ∈ sparse ∪ Set.range (fun k : Fin j.val => 3 * k.val + 3) := by
        right
        exact ⟨⟨i.val, hij⟩, rfl⟩
      have hwi : 3 * i.val + 3 ∈ sparse ∪ Set.range (fun k : Fin i.val => 3 * k.val + 3) := by
        rw [heq]
        exact hwj
      rcases hwi with hs | he
      · exact special_not_mem_sparse i.val hs
      · rcases he with ⟨k, hk⟩
        have := special_injective hk
        omega

noncomputable def inputBound (t : ℕ) (xs : Fin (t + 1) → ℕ) : ℕ :=
  Finset.univ.sup xs

lemma input_le_bound {t : ℕ} (xs : Fin (t + 1) → ℕ) (i : Fin (t + 1)) :
    xs i ≤ inputBound t xs := by
  exact Finset.le_sup (s := Finset.univ) (f := xs) (Finset.mem_univ i)

noncomputable def powerGen : Stage3Case024.OnlineGenerator :=
  fun t xs _ => 2 ^ (inputBound t xs + t + 1)

noncomputable def powerOutput (input : Stage3Case024.Stream) : Stage3Case024.Stream :=
  fun t => powerGen t (fun i => input i) (fun _ => 0)

lemma powerOutput_eq (input : Stage3Case024.Stream) (t : ℕ) :
    powerOutput input t = 2 ^ (inputBound t (fun i => input i) + t + 1) := rfl

lemma bound_mono {input : Stage3Case024.Stream} {s t : ℕ} (hst : s ≤ t) :
    inputBound s (fun i => input i) ≤ inputBound t (fun i => input i) := by
  unfold inputBound
  apply Finset.sup_le
  intro i hi
  exact Finset.le_sup (s := Finset.univ) (f := fun i : Fin (t + 1) => input i)
    (Finset.mem_univ ⟨i.val, by omega⟩)

lemma powerOutput_gt_input (input : Stage3Case024.Stream) (t : ℕ) (i : Fin (t + 1)) :
    input i < powerOutput input t := by
  rw [powerOutput_eq]
  have hle := input_le_bound (fun i : Fin (t + 1) => input i) i
  have hpow : inputBound t (fun i => input i) + t + 1 <
      2 ^ (inputBound t (fun i => input i) + t + 1) := Nat.lt_two_pow_self
  omega

lemma powerOutput_strictMono (input : Stage3Case024.Stream) :
    StrictMono (powerOutput input) := by
  intro s t hst
  rw [powerOutput_eq, powerOutput_eq]
  apply Nat.pow_lt_pow_right (by omega)
  have hb := bound_mono (input := input) (Nat.le_of_lt hst)
  omega

lemma powerOutput_novel (input : Stage3Case024.Stream) :
    GenLimit.NovelGeneratesInLimit input (powerOutput input) sparse := by
  refine ⟨0, fun t _ => ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨inputBound t (fun i => input i) + t + 1, powerOutput_eq input t⟩
  · intro hmem
    simp only [GenLimit.sample, Finset.mem_image, Finset.mem_range] at hmem
    rcases hmem with ⟨s, hs, heq⟩
    have hlt := powerOutput_gt_input input t ⟨s, hs⟩
    exact (Nat.ne_of_lt hlt) heq
  · intro s hst
    exact ne_of_lt (powerOutput_strictMono input hst)

lemma powerGen_follows (input : Stage3Case024.Stream) :
    Stage3Case024.Follows powerGen input (powerOutput input) := by
  intro t
  rfl

lemma family_globallyFeasible {r : ℕ} (hr : 2 ≤ r) :
    Stage3Case024.GloballyFeasible (family r) := by
  refine ⟨powerGen, fun input hlegal => ⟨powerOutput input, powerGen_follows input, ?_⟩⟩
  intro j
  have hnovel := powerOutput_novel input
  rcases hnovel with ⟨T, hT⟩
  refine ⟨T, fun t ht => ?_⟩
  have hres := hT t ht
  exact ⟨sparse_subset_family j hres.1, hres.2.1, hres.2.2⟩

lemma pairObstruction_sparse_univ :
    Stage3Case024.PairObstruction sparse Set.univ swapPerm := by
  intro Ω _ μ _ gen output _ _ hintSparse _ hvalidSparse _
  have hzeroAE : ∀ᵐ ω ∂μ,
      Stage3Case024.relativeUpperDensity
        (GenLimit.GeneratorFirst swapPerm (output ω)) Set.univ = 0 :=
    hvalidSparse.mono (fun ω hω =>
      relativeUpperDensity_generatorFirst_univ_zero hω)
  have hunivZero :
      Stage3Case024.expectedUpperDensity μ Set.univ swapPerm output = 0 := by
    unfold Stage3Case024.expectedUpperDensity
    rw [integral_congr_ae hzeroAE]
    simp
  have hleAE :
      (fun ω => Stage3Case024.relativeUpperDensity
        (GenLimit.GeneratorFirst swapPerm (output ω)) sparse) ≤ᶠ[ae μ]
      (fun _ => (1 : ℝ)) :=
    ae_of_all μ (fun ω => relativeUpperDensity_le_one _ _)
  have hsparseLe :
      Stage3Case024.expectedUpperDensity μ sparse swapPerm output ≤ 1 := by
    unfold Stage3Case024.expectedUpperDensity
    calc
      (∫ ω, Stage3Case024.relativeUpperDensity
          (GenLimit.GeneratorFirst swapPerm (output ω)) sparse ∂μ) ≤
          ∫ _ω, (1 : ℝ) ∂μ :=
        integral_mono_ae hintSparse (integrable_const 1) hleAE
      _ = 1 := by simp
  constructor
  · rw [hunivZero, add_zero]
    exact hsparseLe
  · intro hboth
    rw [hunivZero] at hboth
    norm_num at hboth

lemma family_manyTargetObstruction {r : ℕ} (hr : 2 ≤ r) :
    Stage3Case024.ManyTargetObstruction (family r) swapPerm := by
  intro Ω _ μ _ gen output _ _ _ hvalid
  have hvalidSparse := hvalid ⟨0, by omega⟩
  have hsparseAE : ∀ᵐ ω ∂μ,
      GenLimit.NovelGeneratesInLimit swapPerm (output ω) sparse := by
    filter_upwards [hvalidSparse] with ω hω
    simpa only [family_zero hr] using hω
  let last : Fin r := ⟨r - 1, by omega⟩
  refine ⟨last, ?_⟩
  have hzeroAE : ∀ᵐ ω ∂μ,
      Stage3Case024.relativeUpperDensity
        (GenLimit.GeneratorFirst swapPerm (output ω)) (family r last) = 0 := by
    filter_upwards [hsparseAE] with ω hω
    rw [show family r last = Set.univ by simpa [last] using family_last hr]
    exact relativeUpperDensity_generatorFirst_univ_zero hω
  unfold Stage3Case024.expectedUpperDensity
  rw [integral_congr_ae hzeroAE]
  simp

lemma sparse_ssubset_univ : sparse ⊂ (Set.univ : Set ℕ) := by
  refine Set.ssubset_iff_subset_ne.mpr ⟨Set.subset_univ _, ?_⟩
  intro heq
  have hthree : 3 ∈ sparse := by
    rw [heq]
    trivial
  exact special_not_mem_sparse 0 hthree

end

end Case024

theorem stage3_result : Stage3Case024.MainClaim := by
  constructor
  · refine ⟨Case024.sparse, Set.univ, Case024.swapPerm,
      Case024.sparse_ssubset_univ, Case024.swapPerm_legal_sparse,
      Case024.swapPerm_legal_univ, Case024.pairObstruction_sparse_univ⟩
  · intro r hr
    refine ⟨Case024.family r, Case024.swapPerm, ?_, ?_, ?_, ?_⟩
    · exact Case024.family_strictlyNested hr
    · intro j
      exact Case024.swapPerm_legal_of_sparse_subset _
        (Case024.sparse_subset_family j)
    · exact Case024.family_globallyFeasible hr
    · exact Case024.family_manyTargetObstruction hr
