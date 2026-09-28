import Stage3Model
import GenLimit.Paper17_InfiniteContamination.SharedVanishingPresentation
import Mathlib.Analysis.SpecificLimits.Basic

open Filter MeasureTheory
open scoped Topology BigOperators

namespace Case024Proof

open Stage3Case024
open GenLimit.InfiniteContamination

abbrev Core : Set ℕ := {n | SparseSquare n}

lemma core_infinite : Core.Infinite := by
  exact Set.infinite_range_of_injective (f := fun n : ℕ => n * n) (by
    intro a b h
    nlinarith)

lemma core_strict_univ : Core ⊂ (Set.univ : Set ℕ) := by
  refine ⟨Set.subset_univ _, ?_⟩
  intro h
  have hs : SparseSquare 2 := h (Set.mem_univ 2)
  have hn : ¬ SparseSquare 2 := by
    simpa [sparseBetweenSquares] using sparseBetweenSquares_nonsquare 0
  exact hn hs

noncomputable def commonInput : Stream :=
  sparseMergePresentation Core (Set.univ \ Core) core_infinite

lemma commonInput_injective : Function.Injective commonInput := by
  exact sparseMergePresentation_injective core_infinite Set.disjoint_sdiff_right

lemma commonInput_range : Set.range commonInput = Set.univ := by
  rw [commonInput, range_sparseMergePresentation core_infinite]
  simp

lemma legal_commonInput (K : Language) (hcore : Core ⊆ K) (hinf : K.Infinite) :
    Legal commonInput K := by
  refine ⟨hinf, commonInput_injective, ?_, ?_⟩
  · intro x hx
    rw [commonInput_range]
    exact Set.mem_univ x
  · exact sparseMergePresentation_vanishingNoise_of_core_subset core_infinite hcore

lemma prefixCount_mono {A B : Set ℕ} (h : A ⊆ B) (n : ℕ) :
    GenLimit.PatientScope.prefixCount A n ≤
      GenLimit.PatientScope.prefixCount B n := by
  classical
  unfold GenLimit.PatientScope.prefixCount GenLimit.PatientScope.prefixFinset
  apply Finset.card_le_card
  intro x hx
  exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hx).1, h (Finset.mem_filter.mp hx).2⟩

lemma prefixCount_union_le (A B : Set ℕ) (n : ℕ) :
    GenLimit.PatientScope.prefixCount (A ∪ B) n ≤
      GenLimit.PatientScope.prefixCount A n +
        GenLimit.PatientScope.prefixCount B n := by
  classical
  unfold GenLimit.PatientScope.prefixCount GenLimit.PatientScope.prefixFinset
  simp only [Set.mem_union]
  rw [Finset.filter_or]
  exact Finset.card_union_le _ _

lemma prefixCount_finite_le {F : Set ℕ} (hF : F.Finite) (n : ℕ) :
    GenLimit.PatientScope.prefixCount F n ≤ hF.toFinset.card := by
  classical
  unfold GenLimit.PatientScope.prefixCount GenLimit.PatientScope.prefixFinset
  apply Finset.card_le_card
  intro x hx
  exact hF.mem_toFinset.mpr (Finset.mem_filter.mp hx).2

lemma prefixCount_core_le (n : ℕ) :
    GenLimit.PatientScope.prefixCount Core n ≤ Nat.sqrt n + 1 := by
  simpa [GenLimit.PatientScope.prefixCount, GenLimit.PatientScope.prefixFinset,
    Core, Nat.count_eq_card_filter_range] using count_sparseSquare_le_sqrt_add_one n

lemma prefixCount_univ (n : ℕ) :
    GenLimit.PatientScope.prefixCount (Set.univ : Set ℕ) n = n := by
  simp [GenLimit.PatientScope.prefixCount, GenLimit.PatientScope.prefixFinset]

lemma relativeUpperDensity_le_one (A K : Language) :
    relativeUpperDensity A K ≤ 1 := by
  unfold relativeUpperDensity
  apply limsup_le_of_le
  · exact isCoboundedUnder_le_of_le atTop (fun n => by positivity)
  · exact Eventually.of_forall fun n => by
      have hcount : GenLimit.PatientScope.prefixCount (A ∩ K) n ≤
          GenLimit.PatientScope.prefixCount K n :=
        prefixCount_mono (Set.inter_subset_right) n
      by_cases hz : GenLimit.PatientScope.prefixCount K n = 0
      · simp [hz]
      · have hpos : (0 : ℝ) < GenLimit.PatientScope.prefixCount K n := by
          exact_mod_cast Nat.pos_of_ne_zero hz
        rw [div_le_one hpos]
        exact_mod_cast hcount

lemma relativeUpperDensity_univ_eq_zero_of_subset_core_finite
    {A F : Set ℕ} (hF : F.Finite) (hA : A ⊆ Core ∪ F) :
    relativeUpperDensity A Set.univ = 0 := by
  unfold relativeUpperDensity
  have htend : Tendsto
      (fun n : ℕ =>
        ((Nat.sqrt n : ℝ) + 1 + hF.toFinset.card) / (n : ℝ))
      atTop (𝓝 0) := by
    simpa [add_div] using
      tendsto_sparseSqrt_add_one_div.add
        (tendsto_const_div_atTop_nhds_zero_nat (hF.toFinset.card : ℝ))
  apply Tendsto.limsup_eq
  apply squeeze_zero' (g := fun n : ℕ =>
    ((Nat.sqrt n : ℝ) + 1 + hF.toFinset.card) / (n : ℝ))
    (Eventually.of_forall fun n => by positivity)
  · filter_upwards [] with n
    simp only [Set.inter_univ]
    rw [prefixCount_univ]
    have h1 := prefixCount_mono hA n
    have h2 := prefixCount_union_le Core F n
    have h3 := prefixCount_core_le n
    have h4 := prefixCount_finite_le hF n
    have hnat : GenLimit.PatientScope.prefixCount A n ≤
        Nat.sqrt n + 1 + hF.toFinset.card :=
      h1.trans (h2.trans (Nat.add_le_add h3 h4))
    exact div_le_div_of_nonneg_right (by exact_mod_cast hnat) (by positivity)
  · exact htend

lemma generatorFirst_subset_core_finite {input output : Stream}
    (hvalid : GenLimit.NovelGeneratesInLimit input output Core) :
    ∃ F : Set ℕ, F.Finite ∧ GenLimit.GeneratorFirst input output ⊆ Core ∪ F := by
  obtain ⟨T, hT⟩ := hvalid
  refine ⟨output '' Set.Iio T, (Set.finite_Iio T).image output, ?_⟩
  intro x hx
  rcases hx with ⟨t, rfl, -⟩
  by_cases ht : T ≤ t
  · exact Set.mem_union_left _ (hT t ht).1
  · exact Set.mem_union_right _ ⟨t, Nat.lt_of_not_ge ht, rfl⟩

lemma density_univ_zero_of_valid {input output : Stream}
    (hvalid : GenLimit.NovelGeneratesInLimit input output Core) :
    relativeUpperDensity (GenLimit.GeneratorFirst input output) Set.univ = 0 := by
  obtain ⟨F, hF, hsub⟩ := generatorFirst_subset_core_finite hvalid
  exact relativeUpperDensity_univ_eq_zero_of_subset_core_finite hF hsub

noncomputable def squareGenerator : OnlineGenerator :=
  fun t input _ => (t + 1 + ∑ i, input i) ^ 2

noncomputable def squareOutput (input : Stream) : Stream :=
  fun t => (t + 1 + ∑ i : Fin (t + 1), input i) ^ 2

lemma squareOutput_follows (input : Stream) :
    Follows squareGenerator input (squareOutput input) := by
  intro t
  rfl

lemma input_le_base (input : Stream) (t : ℕ) (i : Fin (t + 1)) :
    input i < t + 1 + ∑ j : Fin (t + 1), input j := by
  have hle : input i ≤ ∑ j : Fin (t + 1), input j := by
    exact Finset.single_le_sum (f := fun j : Fin (t + 1) => input j)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  omega

lemma squareOutput_gt_input (input : Stream) (t : ℕ) (i : Fin (t + 1)) :
    input i < squareOutput input t := by
  have hb := input_le_base input t i
  have hpos : 0 < t + 1 + ∑ j : Fin (t + 1), input j := by omega
  simp only [squareOutput]
  nlinarith [Nat.le_mul_self (t + 1 + ∑ j : Fin (t + 1), input j)]

lemma squareOutput_strictMono (input : Stream) : StrictMono (squareOutput input) := by
  apply strictMono_nat_of_lt_succ
  intro t
  have hsum : (∑ i : Fin (t + 1), input i) ≤
      ∑ i : Fin (t + 2), input i := by
    have hnew := Fin.sum_univ_castSucc (fun i : Fin (t + 2) => input i)
    rw [hnew]
    have heq : (∑ i : Fin (t + 1), input i.castSucc) =
        ∑ i : Fin (t + 1), input i := by
      apply Finset.sum_congr rfl
      intro i _
      rfl
    rw [heq]
    omega
  simp only [squareOutput]
  have hbase : t + 1 + (∑ i : Fin (t + 1), input i) <
      (t + 1) + 1 + (∑ i : Fin (t + 2), input i) := by omega
  exact Nat.pow_lt_pow_left hbase (by omega)

lemma squareOutput_valid (input : Stream) :
    GenLimit.NovelGeneratesInLimit input (squareOutput input) Core := by
  refine ⟨0, ?_⟩
  intro t _
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨t + 1 + ∑ i : Fin (t + 1), input i, by
      simp [squareOutput, Core, SparseSquare, Nat.pow_two]⟩
  · intro hx
    rcases GenLimit.mem_sample_iff.mp hx with ⟨s, hs, heq⟩
    have hlt := squareOutput_gt_input input t ⟨s, hs⟩
    exact hlt.ne (by simpa using heq)
  · intro s hs heq
    exact (squareOutput_strictMono input hs).ne heq

lemma globallyFeasible_family {r : ℕ} (family : Fin r → Language)
    (hcore : ∀ j, Core ⊆ family j) : GloballyFeasible family := by
  refine ⟨squareGenerator, ?_⟩
  intro input _
  refine ⟨squareOutput input, squareOutput_follows input, ?_⟩
  intro j
  obtain ⟨T, hT⟩ := squareOutput_valid input
  refine ⟨T, ?_⟩
  intro t ht
  obtain ⟨hmem, hfresh, hnovel⟩ := hT t ht
  exact ⟨hcore j hmem, hfresh, hnovel⟩

noncomputable def earlyNonSquares (i : ℕ) : Set ℕ :=
  sparseBetweenSquares '' Set.Iio i

lemma earlyNonSquares_finite (i : ℕ) : (earlyNonSquares i).Finite :=
  (Set.finite_Iio i).image sparseBetweenSquares

noncomputable def family (r : ℕ) (i : Fin r) : Language :=
  if (i : ℕ) = r - 1 then Set.univ else Core ∪ earlyNonSquares i

lemma family_core_subset {r : ℕ} (i : Fin r) : Core ⊆ family r i := by
  intro x hx
  simp only [family]
  split
  · exact Set.mem_univ x
  · exact Set.mem_union_left _ hx

lemma family_infinite {r : ℕ} (i : Fin r) : (family r i).Infinite :=
  core_infinite.mono (family_core_subset i)


lemma family_zero_eq_core {r : ℕ} (hr : 2 ≤ r) :
    family r ⟨0, by omega⟩ = Core := by
  have hne : 0 ≠ r - 1 := by omega
  rw [family, if_neg hne]
  simp [earlyNonSquares]

lemma family_last_eq_univ {r : ℕ} (hr : 2 ≤ r) :
    family r ⟨r - 1, by omega⟩ = Set.univ := by
  simp [family]

lemma family_strictlyNested {r : ℕ} (hr : 2 ≤ r) : StrictlyNested (family r) := by
  intro i j hij
  have hjpos : (j : ℕ) < r := j.isLt
  by_cases hjlast : (j : ℕ) = r - 1
  · unfold family
    rw [if_pos hjlast]
    refine ⟨Set.subset_univ _, ?_⟩
    intro heq
    have hifirst : (i : ℕ) ≠ r - 1 := by omega
    rw [if_neg hifirst] at heq
    let w := sparseBetweenSquares i
    have hwcore : w ∉ Core := sparseBetweenSquares_nonsquare i
    have hwearly : w ∉ earlyNonSquares i := by
      rintro ⟨k, hk, hki⟩
      change sparseBetweenSquares k = sparseBetweenSquares i at hki
      have hki' : k = i := sparseBetweenSquares_strictMono.injective hki
      exact (Nat.lt_irrefl i) (hki' ▸ hk)
    have hw : w ∈ Core ∪ earlyNonSquares i := heq (Set.mem_univ w)
    exact hw.elim hwcore hwearly
  · have hilast : (i : ℕ) ≠ r - 1 := by omega
    unfold family
    rw [if_neg hilast, if_neg hjlast]
    refine ⟨?_, ?_⟩
    · apply Set.union_subset_union_right
      apply Set.image_mono
      intro k hk
      exact lt_of_lt_of_le hk hij.le
    · intro heq
      let w := sparseBetweenSquares i
      have hwj : w ∈ earlyNonSquares j := ⟨i, hij, rfl⟩
      have hwi : w ∉ earlyNonSquares i := by
        rintro ⟨k, hk, hki⟩
        change sparseBetweenSquares k = sparseBetweenSquares i at hki
        have hki' : k = i := sparseBetweenSquares_strictMono.injective hki
        exact (Nat.lt_irrefl i) (hki' ▸ hk)
      have hwcore : w ∉ Core := sparseBetweenSquares_nonsquare i
      have hw : w ∈ Core ∪ earlyNonSquares i :=
        heq (Set.mem_union_right _ hwj)
      exact hw.elim hwcore hwi

lemma pairObstruction_core_univ :
    PairObstruction Core Set.univ commonInput := by
  intro Ω _ μ _ gen output _hfollow _hmeas hintCore _hintUniv hvalidCore _hvalidUniv
  have hzeroAE :
      (fun ω => relativeUpperDensity
        (GenLimit.GeneratorFirst commonInput (output ω)) Set.univ) =ᶠ[ae μ]
        (fun _ => 0) :=
    hvalidCore.mono fun ω hω => density_univ_zero_of_valid hω
  have hzero : expectedUpperDensity μ Set.univ commonInput output = 0 := by
    unfold expectedUpperDensity
    rw [integral_congr_ae hzeroAE]
    simp
  have hle : expectedUpperDensity μ Core commonInput output ≤ 1 := by
    unfold expectedUpperDensity
    have hmono := integral_mono_ae hintCore (integrable_const (1 : ℝ))
      (Eventually.of_forall fun ω =>
        relativeUpperDensity_le_one
          (GenLimit.GeneratorFirst commonInput (output ω)) Core)
    simpa using hmono
  constructor
  · simpa [hzero] using hle
  · rintro ⟨hcore, huniv⟩
    rw [hzero] at huniv
    norm_num at huniv

lemma manyTargetObstruction_family {r : ℕ} (hr : 2 ≤ r) :
    ManyTargetObstruction (family r) commonInput := by
  intro Ω _ μ _ gen output _hfollow _hmeas _hint hvalid
  let first : Fin r := ⟨0, by omega⟩
  let last : Fin r := ⟨r - 1, by omega⟩
  have hvalidCore := hvalid first
  have hfirst : family r first = Core := by
    simpa [first] using family_zero_eq_core hr
  rw [hfirst] at hvalidCore
  have hzeroAE :
      (fun ω => relativeUpperDensity
        (GenLimit.GeneratorFirst commonInput (output ω)) Set.univ) =ᶠ[ae μ]
        (fun _ => 0) :=
    hvalidCore.mono fun ω hω => density_univ_zero_of_valid hω
  refine ⟨last, ?_⟩
  have hlast : family r last = Set.univ := by
    simpa [last] using family_last_eq_univ hr
  unfold expectedUpperDensity
  rw [hlast, integral_congr_ae hzeroAE]
  simp

lemma manyTargetWitness_family {r : ℕ} (hr : 2 ≤ r) :
    ManyTargetWitness (family r) commonInput := by
  refine ⟨family_strictlyNested hr, ?_,
    globallyFeasible_family (family := family r) family_core_subset,
    manyTargetObstruction_family hr⟩
  intro j
  exact legal_commonInput (family r j) (family_core_subset j) (family_infinite j)


end Case024Proof

open Filter MeasureTheory
open scoped Topology

open Stage3Case024
open Case024Proof

theorem stage3_result : Stage3Case024.MainClaim := by
  constructor
  · refine ⟨Core, Set.univ, commonInput, core_strict_univ, ?_, ?_,
      pairObstruction_core_univ⟩
    · exact legal_commonInput Core (Set.Subset.rfl) core_infinite
    · exact legal_commonInput Set.univ (Set.subset_univ _) Set.infinite_univ
  · intro r hr
    exact ⟨family r, commonInput, manyTargetWitness_family hr⟩
