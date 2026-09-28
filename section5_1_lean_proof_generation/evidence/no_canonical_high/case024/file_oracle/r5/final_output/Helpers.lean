import Stage3Model
import GenLimit.Paper17_InfiniteContamination.SharedVanishingPresentation
import Mathlib.Data.Nat.Nth

open Filter MeasureTheory
open scoped Topology

namespace Case024

open GenLimit
open GenLimit.InfiniteContamination

abbrev Language := Stage3Case024.Language
abbrev Stream := Stage3Case024.Stream

noncomputable local instance : DecidablePred SparseSquare := Classical.decPred _

/-- The sparse common core used by all targets. -/
def core : Language := {n | SparseSquare n}

/-- Canonical nonsquares used to make the finite intermediate targets strict. -/
def marker (i : ℕ) : ℕ := sparseBetweenSquares i

lemma core_infinite : core.Infinite := by
  let f : ℕ → ℕ := fun n => n * n
  have hf : Function.Injective f := by
    intro a b hab
    exact Nat.mul_self_inj.mp hab
  apply (Set.infinite_range_of_injective hf).mono
  rintro _ ⟨n, rfl⟩
  exact sparseSquare_mul_self n

lemma marker_not_core (i : ℕ) : marker i ∉ core := by
  exact sparseBetweenSquares_nonsquare i

lemma marker_injective : Function.Injective marker :=
  sparseBetweenSquares_strictMono.injective

/-- A full-coverage version of the supplied common sparse presentation. -/
lemma exists_common_legal
    (family : ℕ → Language) (S : Finset ℕ) (hS : S.Nonempty)
    (hcoreSub : ∀ i, i ∈ S → core ⊆ family i) :
    ∃ input : Stream, ∀ i, i ∈ S → Stage3Case024.Legal input (family i) := by
  classical
  let common := finiteCommonCore (indexedLanguages family S)
  let union := finiteIndexedUnion family S
  let exceptional := union \ common
  have hcommon : common.Infinite := by
    apply core_infinite.mono
    intro x hx
    intro L hL
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hL
    exact hcoreSub i hi hx
  have hdisjoint : Disjoint common exceptional := Set.disjoint_sdiff_right
  let input := sparseMergePresentation common exceptional hcommon
  have hinjective : Function.Injective input :=
    sparseMergePresentation_injective hcommon hdisjoint
  have hrange : Set.range input = union := by
    calc
      Set.range input = common ∪ exceptional := range_sparseMergePresentation hcommon
      _ = union := commonCore_union_exceptional_eq_union family S hS
  refine ⟨input, ?_⟩
  intro i hi
  have hcommonFamily : common ⊆ family i := indexedCommonCore_subset family hi
  have hcover : NoOmissions input (family i) := by
    rw [NoOmissions, hrange]
    exact family_subset_finiteIndexedUnion family hi
  have hnoise : VanishingNoise input (family i) :=
    sparseMergePresentation_vanishingNoise_of_core_subset hcommon hcommonFamily
  exact ⟨(hcommon.mono hcommonFamily), hinjective, hcover, hnoise⟩

end Case024

namespace Case024

open GenLimit
open GenLimit.InfiniteContamination

noncomputable local instance : DecidablePred SparseSquare := Classical.decPred _

lemma prefixCount_mono {A B : Language} (hAB : A ⊆ B) (n : ℕ) :
    GenLimit.PatientScope.prefixCount A n ≤
      GenLimit.PatientScope.prefixCount B n := by
  classical
  unfold GenLimit.PatientScope.prefixCount GenLimit.PatientScope.prefixFinset
  exact Finset.card_le_card (by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_range] at hx ⊢
    exact ⟨hx.1, hAB hx.2⟩)

lemma relativeUpperDensity_le_one (A K : Language) :
    Stage3Case024.relativeUpperDensity A K ≤ 1 := by
  unfold Stage3Case024.relativeUpperDensity
  apply limsup_le_of_le
  · apply isCoboundedUnder_le_of_le atTop
    intro n
    exact div_nonneg (by positivity) (by positivity)
  · apply Eventually.of_forall
    intro n
    let a := GenLimit.PatientScope.prefixCount (A ∩ K) n
    let b := GenLimit.PatientScope.prefixCount K n
    have hab : a ≤ b := prefixCount_mono Set.inter_subset_right n
    by_cases hb : b = 0
    · have ha : a = 0 := by omega
      simp [a, b, ha, hb]
    · rw [div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hb)]
      exact_mod_cast hab

lemma prefixCount_union_le (A B : Language) (n : ℕ) :
    GenLimit.PatientScope.prefixCount (A ∪ B) n ≤
      GenLimit.PatientScope.prefixCount A n +
        GenLimit.PatientScope.prefixCount B n := by
  classical
  unfold GenLimit.PatientScope.prefixCount GenLimit.PatientScope.prefixFinset
  let FA := (Finset.range n).filter (fun x => x ∈ A)
  let FB := (Finset.range n).filter (fun x => x ∈ B)
  have hsub : (Finset.range n).filter (fun x => x ∈ A ∪ B) ⊆ FA ∪ FB := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_range, Set.mem_union] at hx
    rcases hx.2 with hxA | hxB
    · exact Finset.mem_union_left _ (by simp [FA, hx.1, hxA])
    · exact Finset.mem_union_right _ (by simp [FB, hx.1, hxB])
  simpa [FA, FB] using (Finset.card_le_card hsub).trans (Finset.card_union_le FA FB)

lemma prefixCount_finite_le {F : Language} (hF : F.Finite) (n : ℕ) :
    GenLimit.PatientScope.prefixCount F n ≤ hF.toFinset.card := by
  classical
  unfold GenLimit.PatientScope.prefixCount GenLimit.PatientScope.prefixFinset
  apply Finset.card_le_card
  intro x hx
  exact (Set.Finite.mem_toFinset hF).mpr (Finset.mem_filter.mp hx).2

lemma prefixCount_core (n : ℕ) :
    GenLimit.PatientScope.prefixCount core n = Nat.count SparseSquare n := by
  classical
  rw [Nat.count_eq_card_filter_range]
  rfl

lemma relativeUpperDensity_univ_eq_zero_of_finite_diff
    {A : Language} (hfinite : (A \ core).Finite) :
    Stage3Case024.relativeUpperDensity A Set.univ = 0 := by
  let F : Language := A \ core
  let B : ℕ := hfinite.toFinset.card
  have hsubset : A ⊆ core ∪ F := by
    intro x hx
    by_cases hxc : x ∈ core
    · exact Or.inl hxc
    · exact Or.inr ⟨hx, hxc⟩
  let ratio : ℕ → ℝ := fun n =>
    (GenLimit.PatientScope.prefixCount (A ∩ Set.univ) n : ℝ) /
      (GenLimit.PatientScope.prefixCount (Set.univ : Language) n : ℝ)
  let upper : ℕ → ℝ := fun n => ((Nat.sqrt n : ℝ) + 1 + B) / n
  have hbound : ∀ n, ratio n ≤ upper n := by
    intro n
    have hcount : GenLimit.PatientScope.prefixCount A n ≤ Nat.sqrt n + 1 + B := by
      calc
        GenLimit.PatientScope.prefixCount A n ≤
            GenLimit.PatientScope.prefixCount (core ∪ F) n :=
          prefixCount_mono hsubset n
        _ ≤ GenLimit.PatientScope.prefixCount core n +
              GenLimit.PatientScope.prefixCount F n := prefixCount_union_le core F n
        _ ≤ (Nat.sqrt n + 1) + B := by
          rw [prefixCount_core]
          exact Nat.add_le_add
            (count_sparseSquare_le_sqrt_add_one n)
            (prefixCount_finite_le hfinite n)
    change (GenLimit.PatientScope.prefixCount (A ∩ Set.univ) n : ℝ) /
        (GenLimit.PatientScope.prefixCount (Set.univ : Language) n : ℝ) ≤ _
    simp only [Set.inter_univ]
    have huniv : GenLimit.PatientScope.prefixCount (Set.univ : Language) n = n := by
      simp [GenLimit.PatientScope.prefixCount, GenLimit.PatientScope.prefixFinset]
    rw [huniv]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hcount) (by positivity)
  have hupper : Tendsto upper atTop (𝓝 0) := by
    have hB : Tendsto (fun n : ℕ => (B : ℝ) / n) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    simpa [upper, add_div] using tendsto_sparseSqrt_add_one_div.add hB
  have hratio : Tendsto ratio atTop (𝓝 0) := by
    apply squeeze_zero'
    · exact Eventually.of_forall (fun n => div_nonneg (by positivity) (by positivity))
    · exact Eventually.of_forall hbound
    · exact hupper
  unfold Stage3Case024.relativeUpperDensity
  exact hratio.limsup_eq

lemma generatorFirst_diff_finite_of_eventual_core
    {input output : Stream}
    (h : GenLimit.NovelGeneratesInLimit input output core) :
    (GenLimit.GeneratorFirst input output \ core).Finite := by
  obtain ⟨T, hT⟩ := h
  let E : Set ℕ := Set.range (fun t : Fin T => output t)
  have hE : E.Finite := Set.toFinite E
  apply hE.subset
  rintro x ⟨⟨t, hout, -⟩, hxcore⟩
  have ht : t < T := by
    by_contra hnot
    exact hxcore (hout ▸ (hT t (Nat.le_of_not_gt hnot)).1)
  exact ⟨⟨t, ht⟩, hout⟩

end Case024

namespace Case024

open GenLimit
open GenLimit.InfiniteContamination

noncomputable def extension (j : ℕ) : Language :=
  core ∪ (↑((Finset.range j).image marker) : Set ℕ)

lemma core_subset_extension (j : ℕ) : core ⊆ extension j :=
  Set.subset_union_left

lemma extension_mono {i j : ℕ} (hij : i ≤ j) : extension i ⊆ extension j := by
  classical
  intro x hx
  rcases hx with hx | hx
  · exact Or.inl hx
  · apply Or.inr
    simp only [Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_image] at hx ⊢
    obtain ⟨k, hk, rfl⟩ := hx
    exact ⟨k, Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hk) hij), rfl⟩

lemma marker_mem_extension_of_lt {i j : ℕ} (hij : i < j) : marker i ∈ extension j := by
  right
  exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hij, rfl⟩

lemma marker_not_mem_extension_self (i : ℕ) : marker i ∉ extension i := by
  classical
  rintro (hi | hi)
  · exact marker_not_core i hi
  · obtain ⟨k, hk, hki⟩ := Finset.mem_image.mp hi
    have : k = i := marker_injective hki
    exact (Finset.mem_range.mp hk).ne this

noncomputable def targetFamily (r : ℕ) (j : Fin r) : Language :=
  if (j : ℕ) + 1 = r then Set.univ else extension j

lemma core_subset_targetFamily {r : ℕ} (j : Fin r) : core ⊆ targetFamily r j := by
  classical
  unfold targetFamily
  split
  · exact Set.subset_univ core
  · exact core_subset_extension j

lemma targetFamily_zero {r : ℕ} (hr : 2 ≤ r) :
    targetFamily r ⟨0, by omega⟩ = core := by
  classical
  have hne : (1 : ℕ) ≠ r := by omega
  simp [targetFamily, extension, hne]

lemma targetFamily_last {r : ℕ} (hr : 2 ≤ r) :
    targetFamily r ⟨r - 1, by omega⟩ = Set.univ := by
  classical
  simp [targetFamily]
  omega

lemma targetFamily_strictlyNested {r : ℕ} (hr : 2 ≤ r) :
    Stage3Case024.StrictlyNested (targetFamily r) := by
  classical
  intro i j hij
  have hilast : (i : ℕ) + 1 ≠ r := by omega
  by_cases hjlast : (j : ℕ) + 1 = r
  · rw [show targetFamily r i = extension i by simp [targetFamily, hilast]]
    rw [show targetFamily r j = Set.univ by simp [targetFamily, hjlast]]
    refine ⟨Set.subset_univ (extension i), ?_⟩
    intro hsub
    exact marker_not_mem_extension_self i (hsub (Set.mem_univ _))
  · rw [show targetFamily r i = extension i by simp [targetFamily, hilast]]
    rw [show targetFamily r j = extension j by simp [targetFamily, hjlast]]
    refine ⟨extension_mono (Nat.le_of_lt hij), ?_⟩
    intro hsub
    exact marker_not_mem_extension_self i (hsub (marker_mem_extension_of_lt hij))

lemma exists_legal_targetFamily {r : ℕ} (hr : 2 ≤ r) :
    ∃ input : Stream, ∀ j : Fin r, Stage3Case024.Legal input (targetFamily r j) := by
  classical
  let family : ℕ → Language := fun i =>
    if hi : i < r then targetFamily r ⟨i, hi⟩ else Set.univ
  have hnonempty : (Finset.range r).Nonempty := by
    exact ⟨0, Finset.mem_range.mpr (by omega)⟩
  obtain ⟨input, hinput⟩ := exists_common_legal family (Finset.range r) hnonempty (by
    intro i hi
    simp only [Finset.mem_range] at hi
    simp [family, hi, core_subset_targetFamily])
  refine ⟨input, ?_⟩
  intro j
  simpa [family, j.isLt] using hinput j (Finset.mem_range.mpr j.isLt)

noncomputable def coreGenerator : Stage3Case024.OnlineGenerator :=
  fun t input _ =>
    Nat.nth (fun x => x ∈ core) (t + 1 + ∑ i, input i)

def coreIndex (input : Stream) (t : ℕ) : ℕ :=
  t + 1 + (∑ i ∈ Finset.range (t + 1), input i)

noncomputable def coreOutput (input : Stream) : Stream :=
  fun t => Nat.nth (fun x => x ∈ core) (coreIndex input t)

lemma follows_coreGenerator (input : Stream) :
    Stage3Case024.Follows coreGenerator input (coreOutput input) := by
  intro t
  unfold coreOutput coreGenerator coreIndex
  rw [Fin.sum_univ_eq_sum_range input (t + 1)]

lemma coreOutput_mem (input : Stream) (t : ℕ) : coreOutput input t ∈ core := by
  exact Nat.nth_mem_of_infinite core_infinite _

lemma coreOutput_avoids_input (input : Stream) (t : ℕ) :
    coreOutput input t ∉ GenLimit.sample input (t + 1) := by
  intro hmem
  rw [GenLimit.mem_sample_iff] at hmem
  obtain ⟨s, hst, hs⟩ := hmem
  have hsle : input s ≤ (∑ i ∈ Finset.range (t + 1), input i) := by
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _)
      (Finset.mem_range.mpr hst)
  have hindex : input s < coreIndex input t := by
    unfold coreIndex
    omega
  have hnth : coreIndex input t ≤ coreOutput input t := by
    exact (Nat.nth_strictMono core_infinite).id_le _
  exact (Nat.ne_of_lt (hindex.trans_le hnth)) hs

lemma coreIndex_strictMono (input : Stream) : StrictMono (coreIndex input) := by
  apply strictMono_nat_of_lt_succ
  intro t
  unfold coreIndex
  have hsum : (∑ i ∈ Finset.range (t + 1), input i) ≤
      (∑ i ∈ Finset.range (t + 1 + 1), input i) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.range_mono (by omega)
    · intro i hi _
      exact Nat.zero_le _
  omega

lemma coreOutput_injective (input : Stream) : Function.Injective (coreOutput input) := by
  intro s t hst
  have hnth : coreIndex input s = coreIndex input t := by
    exact Nat.nth_injective core_infinite hst
  exact (coreIndex_strictMono input).injective hnth

lemma coreOutput_novel (input : Stream) :
    GenLimit.NovelGeneratesInLimit input (coreOutput input) core := by
  refine ⟨0, ?_⟩
  intro t _
  exact ⟨coreOutput_mem input t, coreOutput_avoids_input input t,
    fun s hst => (coreOutput_injective input).ne hst.ne⟩

lemma targetFamily_globallyFeasible {r : ℕ} (hr : 2 ≤ r) :
    Stage3Case024.GloballyFeasible (targetFamily r) := by
  refine ⟨coreGenerator, ?_⟩
  intro input _
  refine ⟨coreOutput input, follows_coreGenerator input, ?_⟩
  intro j
  obtain ⟨T, hT⟩ := coreOutput_novel input
  refine ⟨T, ?_⟩
  intro t ht
  obtain ⟨hmem, hfresh, hnovel⟩ := hT t ht
  exact ⟨core_subset_targetFamily j hmem, hfresh, hnovel⟩

end Case024

namespace Case024

open GenLimit
open MeasureTheory

lemma targetFamily_manyTargetObstruction {r : ℕ} (hr : 2 ≤ r) (input : Stream) :
    Stage3Case024.ManyTargetObstruction (targetFamily r) input := by
  intro Ω _ μ _ gen output _ _ _ hvalid
  let last : Fin r := ⟨r - 1, by omega⟩
  let zero : Fin r := ⟨0, by omega⟩
  refine ⟨last, ?_⟩
  have hcoreAE : ∀ᵐ ω ∂μ,
      GenLimit.NovelGeneratesInLimit input (output ω) core := by
    simpa [zero, targetFamily_zero hr] using hvalid zero
  have hzeroAE : ∀ᵐ ω ∂μ,
      Stage3Case024.relativeUpperDensity
        (GenLimit.GeneratorFirst input (output ω)) Set.univ = 0 := by
    filter_upwards [hcoreAE] with ω hω
    exact relativeUpperDensity_univ_eq_zero_of_finite_diff
      (generatorFirst_diff_finite_of_eventual_core hω)
  unfold Stage3Case024.expectedUpperDensity
  rw [show targetFamily r last = Set.univ by simpa [last] using targetFamily_last hr]
  calc
    (∫ ω, Stage3Case024.relativeUpperDensity
      (GenLimit.GeneratorFirst input (output ω)) Set.univ ∂μ) =
        ∫ _ω, (0 : ℝ) ∂μ := integral_congr_ae hzeroAE
    _ = 0 := by simp

lemma targetFamily_manyTargetWitness {r : ℕ} (hr : 2 ≤ r) :
    ∃ input : Stream, Stage3Case024.ManyTargetWitness (targetFamily r) input := by
  obtain ⟨input, hlegal⟩ := exists_legal_targetFamily hr
  refine ⟨input, targetFamily_strictlyNested hr, hlegal,
    targetFamily_globallyFeasible hr, targetFamily_manyTargetObstruction hr input⟩

lemma pairObstruction_core_univ (input : Stream) :
    Stage3Case024.PairObstruction core Set.univ input := by
  intro Ω _ μ _ gen output _ _ hintCore _ hvalidCore _
  have hzeroAE : ∀ᵐ ω ∂μ,
      Stage3Case024.relativeUpperDensity
        (GenLimit.GeneratorFirst input (output ω)) Set.univ = 0 := by
    filter_upwards [hvalidCore] with ω hω
    exact relativeUpperDensity_univ_eq_zero_of_finite_diff
      (generatorFirst_diff_finite_of_eventual_core hω)
  have hzero : Stage3Case024.expectedUpperDensity μ Set.univ input output = 0 := by
    unfold Stage3Case024.expectedUpperDensity
    calc
      (∫ ω, Stage3Case024.relativeUpperDensity
        (GenLimit.GeneratorFirst input (output ω)) Set.univ ∂μ) =
          ∫ _ω, (0 : ℝ) ∂μ := integral_congr_ae hzeroAE
      _ = 0 := by simp
  have hone : Stage3Case024.expectedUpperDensity μ core input output ≤ 1 := by
    unfold Stage3Case024.expectedUpperDensity
    calc
      (∫ ω, Stage3Case024.relativeUpperDensity
        (GenLimit.GeneratorFirst input (output ω)) core ∂μ) ≤
          ∫ _ω, (1 : ℝ) ∂μ := by
            apply integral_mono_ae hintCore (integrable_const 1)
            exact Filter.Eventually.of_forall fun ω =>
              relativeUpperDensity_le_one
                (GenLimit.GeneratorFirst input (output ω)) core
      _ = 1 := by simp
  constructor
  · rw [hzero, add_zero]
    exact hone
  · intro hboth
    rw [hzero] at hboth
    linarith

lemma pairWitness :
    ∃ K₀ K₁ : Language, ∃ input : Stream,
      K₀ ⊂ K₁ ∧ Stage3Case024.Legal input K₀ ∧
        Stage3Case024.Legal input K₁ ∧
        Stage3Case024.PairObstruction K₀ K₁ input := by
  obtain ⟨input, hlegal⟩ := exists_legal_targetFamily (r := 2) (by omega)
  have hzero : targetFamily 2 ⟨0, by omega⟩ = core := targetFamily_zero (by omega)
  have hone : targetFamily 2 ⟨1, by omega⟩ = Set.univ := targetFamily_last (by omega)
  refine ⟨core, Set.univ, input, ?_, ?_, ?_, pairObstruction_core_univ input⟩
  · refine ⟨Set.subset_univ core, ?_⟩
    intro hsub
    exact marker_not_core 0 (hsub (Set.mem_univ _))
  · rw [← hzero]
    exact hlegal ⟨0, by omega⟩
  · rw [← hone]
    exact hlegal ⟨1, by omega⟩

end Case024
