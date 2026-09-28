import Stage3Model
import GenLimit.Paper17_InfiniteContamination.SharedVanishingPresentation
import Mathlib.Tactic

open Filter MeasureTheory
open scoped Topology

namespace Case024

open Stage3Case024

noncomputable local instance : DecidablePred
    GenLimit.InfiniteContamination.SparseSquare := Classical.decPred _

abbrev core : Set ℕ := {n | GenLimit.InfiniteContamination.SparseSquare n}

private theorem squareMap_injective : Function.Injective (fun n : ℕ => n * n) := by
  intro a b hab
  nlinarith

theorem core_infinite : core.Infinite := by
  exact (Set.infinite_range_of_injective squareMap_injective).mono (by
    rintro _ ⟨n, rfl⟩
    exact GenLimit.InfiniteContamination.sparseSquare_mul_self n)

theorem prefixCount_mono {A B : Set ℕ} (h : A ⊆ B) (n : ℕ) :
    GenLimit.PatientScope.prefixCount A n ≤
      GenLimit.PatientScope.prefixCount B n := by
  unfold GenLimit.PatientScope.prefixCount
  apply Finset.card_le_card
  intro x hx
  rw [GenLimit.PatientScope.mem_prefixFinset] at hx ⊢
  exact ⟨hx.1, h hx.2⟩

@[simp] theorem prefixCount_univ (n : ℕ) :
    GenLimit.PatientScope.prefixCount Set.univ n = n := by
  simp [GenLimit.PatientScope.prefixCount, GenLimit.PatientScope.prefixFinset]

private theorem ratio_nonneg (A K : Set ℕ) (n : ℕ) :
    0 ≤ (GenLimit.PatientScope.prefixCount (A ∩ K) n : ℝ) /
      (GenLimit.PatientScope.prefixCount K n : ℝ) := by positivity

private theorem ratio_le_one (A K : Set ℕ) (n : ℕ) :
    (GenLimit.PatientScope.prefixCount (A ∩ K) n : ℝ) /
        (GenLimit.PatientScope.prefixCount K n : ℝ) ≤ 1 := by
  by_cases hz : GenLimit.PatientScope.prefixCount K n = 0
  · simp [hz]
  · apply (div_le_one (by positivity)).2
    exact_mod_cast prefixCount_mono Set.inter_subset_right n

theorem relativeUpperDensity_le_one (A K : Set ℕ) :
    Stage3Case024.relativeUpperDensity A K ≤ 1 := by
  unfold Stage3Case024.relativeUpperDensity
  calc
    limsup (fun n : ℕ =>
      (GenLimit.PatientScope.prefixCount (A ∩ K) n : ℝ) /
        (GenLimit.PatientScope.prefixCount K n : ℝ)) atTop
        ≤ limsup (fun _ : ℕ => (1 : ℝ)) atTop := by
          apply limsup_le_limsup
          exact Eventually.of_forall (ratio_le_one A K)
          exact isCoboundedUnder_le_of_le atTop (ratio_nonneg A K)
          exact isBoundedUnder_of ⟨1, fun _ => le_rfl⟩
    _ = 1 := (tendsto_const_nhds.limsup_eq)

private theorem prefixCount_core_eq_count (n : ℕ) :
    GenLimit.PatientScope.prefixCount core n =
      Nat.count GenLimit.InfiniteContamination.SparseSquare n := by
  classical
  rw [Nat.count_eq_card_filter_range]
  rfl

private theorem prefixCount_union_le (A B : Set ℕ) (n : ℕ) :
    GenLimit.PatientScope.prefixCount (A ∪ B) n ≤
      GenLimit.PatientScope.prefixCount A n +
        GenLimit.PatientScope.prefixCount B n := by
  unfold GenLimit.PatientScope.prefixCount
  let FA := GenLimit.PatientScope.prefixFinset A n
  let FB := GenLimit.PatientScope.prefixFinset B n
  have hsub : GenLimit.PatientScope.prefixFinset (A ∪ B) n ⊆ FA ∪ FB := by
    intro x hx
    rw [GenLimit.PatientScope.mem_prefixFinset] at hx
    rcases hx.2 with hxA | hxB
    · exact Finset.mem_union_left _ (GenLimit.PatientScope.mem_prefixFinset.mpr ⟨hx.1, hxA⟩)
    · exact Finset.mem_union_right _ (GenLimit.PatientScope.mem_prefixFinset.mpr ⟨hx.1, hxB⟩)
  exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)

private theorem prefixCount_finite_le (F : Set ℕ) (hF : F.Finite) (n : ℕ) :
    GenLimit.PatientScope.prefixCount F n ≤ hF.toFinset.card := by
  unfold GenLimit.PatientScope.prefixCount
  apply Finset.card_le_card
  intro x hx
  simp only [Set.Finite.mem_toFinset]
  exact (GenLimit.PatientScope.mem_prefixFinset.mp hx).2

private theorem tendsto_core_union_finite_ratio
    (F : Set ℕ) (hF : F.Finite) :
    Tendsto
      (fun n : ℕ =>
        (GenLimit.PatientScope.prefixCount (core ∪ F) n : ℝ) / (n : ℝ))
      atTop (𝓝 0) := by
  apply squeeze_zero'
  · exact Eventually.of_forall fun n => by positivity
  · refine (eventually_ge_atTop 1).mono ?_
    intro n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    apply (div_le_div_iff_of_pos_right hnpos).2
    calc
      (GenLimit.PatientScope.prefixCount (core ∪ F) n : ℝ)
          ≤ GenLimit.PatientScope.prefixCount core n + hF.toFinset.card := by
            exact_mod_cast (prefixCount_union_le core F n).trans
              (Nat.add_le_add_left (prefixCount_finite_le F hF n) _)
      _ = Nat.count GenLimit.InfiniteContamination.SparseSquare n + hF.toFinset.card := by
            rw [prefixCount_core_eq_count]
      _ ≤ Nat.sqrt n + 1 + hF.toFinset.card := by
            exact_mod_cast Nat.add_le_add_right
              (GenLimit.InfiniteContamination.count_sparseSquare_le_sqrt_add_one n)
              hF.toFinset.card
  · have hconst : Tendsto (fun n : ℕ => (hF.toFinset.card : ℝ) / (n : ℝ))
        atTop (𝓝 0) := by
      simpa [div_eq_mul_inv] using
        (tendsto_const_nhds.mul tendsto_inverse_atTop_nhds_zero_nat)
    convert GenLimit.InfiniteContamination.tendsto_sparseSqrt_add_one_div.add hconst using 1 <;>
      simp [add_div]

theorem relativeUpperDensity_univ_eq_zero_of_subset_core_union_finite
    {A : Set ℕ} (F : Set ℕ) (hF : F.Finite) (hA : A ⊆ core ∪ F) :
    Stage3Case024.relativeUpperDensity A Set.univ = 0 := by
  unfold Stage3Case024.relativeUpperDensity
  apply Filter.Tendsto.limsup_eq
  apply squeeze_zero' (g := fun n : ℕ =>
    (GenLimit.PatientScope.prefixCount (core ∪ F) n : ℝ) / (n : ℝ))
  · exact Eventually.of_forall fun n => ratio_nonneg A Set.univ n
  · refine Eventually.of_forall fun n => ?_
    rw [prefixCount_univ]
    apply div_le_div_of_nonneg_right
    exact_mod_cast prefixCount_mono
      ((Set.inter_subset_left : A ∩ Set.univ ⊆ A).trans hA) n
    positivity
  · simpa using tendsto_core_union_finite_ratio F hF

noncomputable def commonInput : Stream :=
  GenLimit.InfiniteContamination.sparseMergePresentation core (Set.univ \ core) core_infinite

theorem commonInput_legal (K : Language) (hcoreK : core ⊆ K) (hKinf : K.Infinite) :
    Legal commonInput K := by
  refine ⟨hKinf, ?_⟩
  refine ⟨GenLimit.InfiniteContamination.sparseMergePresentation_injective core_infinite
      Set.disjoint_sdiff_right, ?_,
    GenLimit.InfiniteContamination.sparseMergePresentation_vanishingNoise_of_core_subset
      core_infinite hcoreK⟩
  rw [GenLimit.InfiniteContamination.NoOmissions]
  unfold commonInput
  rw [GenLimit.InfiniteContamination.range_sparseMergePresentation core_infinite]
  intro x hx
  simp

noncomputable def coreGenerator : OnlineGenerator := fun t input previous =>
  Classical.choose <| core_infinite.exists_not_mem_finset
    ((Finset.univ.image input) ∪ (Finset.univ.image previous))

theorem coreGenerator_spec (t : ℕ) (input : Fin (t + 1) → ℕ)
    (previous : Fin t → ℕ) :
    coreGenerator t input previous ∈ core ∧
      coreGenerator t input previous ∉ Finset.univ.image input ∧
      coreGenerator t input previous ∉ Finset.univ.image previous := by
  have h := Classical.choose_spec <| core_infinite.exists_not_mem_finset
    ((Finset.univ.image input) ∪ (Finset.univ.image previous))
  simpa [coreGenerator, Finset.mem_union] using h

noncomputable def run (gen : OnlineGenerator) (input : Stream) : Stream :=
  fun t => WellFounded.fix Nat.lt_wfRel.wf
    (fun n rec => gen n (fun i => input i) (fun i => rec i i.isLt)) t

@[simp] theorem run_eq (gen : OnlineGenerator) (input : Stream) (t : ℕ) :
    run gen input t = gen t (fun i => input i) (fun i => run gen input i) := by
  rw [run, WellFounded.fix_eq]
  congr 1

 theorem run_follows (gen : OnlineGenerator) (input : Stream) :
    Follows gen input (run gen input) := by
  intro t
  exact run_eq gen input t

theorem core_run_valid (input : Stream) :
    EventuallyFreshValidPath core input (run coreGenerator input) := by
  refine ⟨0, ?_⟩
  intro t _
  rw [run_eq]
  have hs := coreGenerator_spec t (fun i => input i)
    (fun i => run coreGenerator input i)
  refine ⟨hs.1, ?_, ?_⟩
  · intro hmem
    rw [GenLimit.mem_sample_iff] at hmem
    obtain ⟨i, hi, heq⟩ := hmem
    apply hs.2.1
    exact Finset.mem_image.mpr ⟨⟨i, by omega⟩, Finset.mem_univ _, heq⟩
  · intro s hst heq
    apply hs.2.2
    exact Finset.mem_image.mpr ⟨⟨s, hst⟩, Finset.mem_univ _, heq⟩

end Case024

namespace Case024

open Stage3Case024

abbrev extraPoint := GenLimit.InfiniteContamination.sparseBetweenSquares

noncomputable def extras (n : ℕ) : Set ℕ :=
  ↑((Finset.range n).image extraPoint)

@[simp] theorem mem_extras {n x : ℕ} : x ∈ extras n ↔ ∃ k < n, extraPoint k = x := by
  classical
  simp [extras]

 theorem extras_finite (n : ℕ) : (extras n).Finite := by
  unfold extras
  exact Finset.finite_toSet _

noncomputable def family (r : ℕ) (j : Fin r) : Language :=
  if (j : ℕ) + 1 = r then Set.univ else core ∪ extras j

theorem core_subset_family (r : ℕ) (j : Fin r) : core ⊆ family r j := by
  intro x hx
  simp only [family]
  split
  · exact Set.mem_univ x
  · exact Or.inl hx

theorem family_infinite (r : ℕ) (j : Fin r) : (family r j).Infinite :=
  core_infinite.mono (core_subset_family r j)

theorem family_last_eq_univ {r : ℕ} (hr : 0 < r) :
    family r ⟨r - 1, by omega⟩ = Set.univ := by
  change (if r - 1 + 1 = r then Set.univ else core ∪ extras (r - 1)) = Set.univ
  rw [if_pos (Nat.sub_add_cancel (by omega))]

theorem family_nonlast_eq {r : ℕ} (j : Fin r) (hj : (j : ℕ) + 1 ≠ r) :
    family r j = core ∪ extras j := by
  simp [family, hj]

theorem extraPoint_injective : Function.Injective extraPoint :=
  GenLimit.InfiniteContamination.sparseBetweenSquares_strictMono.injective

theorem extraPoint_not_core (k : ℕ) : extraPoint k ∉ core :=
  GenLimit.InfiniteContamination.sparseBetweenSquares_nonsquare k

theorem strict_family {r : ℕ} (hr : 2 ≤ r) : StrictlyNested (family r) := by
  intro i j hij
  have hiNonlast : (i : ℕ) + 1 ≠ r := by omega
  rw [family_nonlast_eq i hiNonlast]
  by_cases hjlast : (j : ℕ) + 1 = r
  · rw [show family r j = Set.univ by simp [family, hjlast]]
    refine ⟨Set.subset_univ _, ?_⟩
    intro hback
    have hmem : extraPoint i ∈ core ∪ extras i :=
      hback (Set.mem_univ _)
    rcases hmem with hcore | hextra
    · exact extraPoint_not_core i hcore
    · obtain ⟨k, hk, heqki⟩ := mem_extras.mp hextra
      have : k = i := extraPoint_injective heqki
      omega
  · rw [family_nonlast_eq j hjlast]
    refine ⟨?_, ?_⟩
    · intro x hx
      rcases hx with hx | hx
      · exact Or.inl hx
      · exact Or.inr (mem_extras.mpr <| by
          obtain ⟨k, hk, rfl⟩ := mem_extras.mp hx
          exact ⟨k, lt_trans hk hij, rfl⟩)
    · intro hback
      have hmem : extraPoint i ∈ core ∪ extras i :=
        hback (Or.inr (mem_extras.mpr ⟨i, hij, rfl⟩))
      rcases hmem with hcore | hextra
      · exact extraPoint_not_core i hcore
      · obtain ⟨k, hk, heqki⟩ := mem_extras.mp hextra
        have : k = i := extraPoint_injective heqki
        omega

theorem generatorFirst_subset_core_union_finite
    {input output : Stream}
    (hvalid : EventuallyFreshValidPath core input output) :
    ∃ F : Set ℕ, F.Finite ∧ GenLimit.GeneratorFirst input output ⊆ core ∪ F := by
  obtain ⟨T, hT⟩ := hvalid
  let F : Set ℕ := output '' Set.Iio T
  refine ⟨F, (Set.finite_Iio T).image output, ?_⟩
  intro x hx
  obtain ⟨t, hout, -⟩ := hx
  by_cases ht : T ≤ t
  · exact Or.inl (hout ▸ (hT t ht).1)
  · exact Or.inr ⟨t, by simpa using Nat.lt_of_not_ge ht, hout⟩

theorem relativeUpperDensity_generatorFirst_univ_zero
    {input output : Stream}
    (hvalid : EventuallyFreshValidPath core input output) :
    relativeUpperDensity (GenLimit.GeneratorFirst input output) Set.univ = 0 := by
  obtain ⟨F, hF, hsub⟩ := generatorFirst_subset_core_union_finite hvalid
  exact relativeUpperDensity_univ_eq_zero_of_subset_core_union_finite F hF hsub

theorem globallyFeasible_family (r : ℕ) : GloballyFeasible (family r) := by
  refine ⟨coreGenerator, ?_⟩
  intro input _
  refine ⟨run coreGenerator input, run_follows _ _, ?_⟩
  intro j
  obtain ⟨T, hT⟩ := core_run_valid input
  refine ⟨T, ?_⟩
  intro t ht
  obtain ⟨hmem, hfresh, hnovel⟩ := hT t ht
  exact ⟨core_subset_family r j hmem, hfresh, hnovel⟩

end Case024
