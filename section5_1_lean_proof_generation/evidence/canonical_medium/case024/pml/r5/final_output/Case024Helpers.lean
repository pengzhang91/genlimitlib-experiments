import Stage3Model
import GenLimit.Paper17_InfiniteContamination.SharedVanishingPresentation
import GenLimit.Paper39_DenseGeneration.Abstract.TargetDensity
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open Filter MeasureTheory
open scoped Topology

namespace Stage3Case024Proof

open GenLimit
open GenLimit.InfiniteContamination
open GenLimit.PatientScope

abbrev Language := Stage3Case024.Language
abbrev Stream := Stage3Case024.Stream

/-- The ambient-density-zero common core. -/
def squareCore : Language := {n | SparseSquare n}

lemma squareCore_infinite : squareCore.Infinite := by
  have hmono : StrictMono (fun n : ℕ => n * n) := by
    apply strictMono_nat_of_lt_succ
    intro n
    nlinarith
  exact (Set.infinite_range_of_injective hmono.injective).mono (by
    rintro _ ⟨n, rfl⟩
    exact sparseSquare_mul_self n)

lemma squareCore_ne_univ : squareCore ≠ Set.univ := by
  intro h
  have hmem : sparseBetweenSquares 0 ∈ squareCore := by simp [h]
  exact sparseBetweenSquares_nonsquare 0 hmem

noncomputable def commonInput : Stream :=
  sparseMergePresentation squareCore squareCoreᶜ squareCore_infinite

lemma commonInput_injective : Function.Injective commonInput := by
  apply sparseMergePresentation_injective squareCore_infinite
  rw [Set.disjoint_left]
  exact fun _ hx hxcompl => hxcompl hx

lemma commonInput_range : Set.range commonInput = Set.univ := by
  rw [commonInput, range_sparseMergePresentation squareCore_infinite]
  exact Set.union_compl_self squareCore

lemma commonInput_vanishing (K : Language) (hcore : squareCore ⊆ K) :
    VanishingNoise commonInput K := by
  exact sparseMergePresentation_vanishingNoise_of_core_subset
    squareCore_infinite hcore

lemma commonInput_legal (K : Language) (hK : K.Infinite)
    (hcore : squareCore ⊆ K) : Stage3Case024.Legal commonInput K := by
  refine ⟨hK, commonInput_injective, ?_, commonInput_vanishing K hcore⟩
  intro x hx
  rw [commonInput_range]
  exact Set.mem_univ x

lemma prefixCount_squareCore_le (n : ℕ) :
    prefixCount squareCore n ≤ Nat.sqrt n + 1 := by
  simpa [prefixCount, prefixFinset, squareCore, Nat.count_eq_card_filter_range] using
    count_sparseSquare_le_sqrt_add_one n

lemma prefixCount_univ (n : ℕ) : prefixCount (Set.univ : Set ℕ) n = n := by
  simp [prefixCount, prefixFinset]

lemma relativeUpperDensity_nonneg (A K : Language) :
    0 ≤ Stage3Case024.relativeUpperDensity A K := by
  unfold Stage3Case024.relativeUpperDensity
  apply le_limsup_of_frequently_le
  · exact Frequently.of_forall (fun n => div_nonneg (by positivity) (by positivity))
  · exact isBoundedUnder_of ⟨1, fun n => by
      by_cases hzero : prefixCount K n = 0
      · simp [hzero]
      · rw [div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hzero)]
        exact_mod_cast prefixCount_mono Set.inter_subset_right n⟩

lemma relativeUpperDensity_le_one (A K : Language) :
    Stage3Case024.relativeUpperDensity A K ≤ 1 := by
  unfold Stage3Case024.relativeUpperDensity
  apply limsup_le_of_le
  · exact isCoboundedUnder_le_of_le atTop
      (fun n => div_nonneg (by positivity) (by positivity))
  · exact Eventually.of_forall (fun n => by
      by_cases hzero : prefixCount K n = 0
      · simp [hzero]
      · rw [div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hzero)]
        exact_mod_cast prefixCount_mono Set.inter_subset_right n)

lemma relativeUpperDensity_univ_eq_zero_of_subset_finite
    {A F : Language} (hF : F.Finite) (hsub : A ⊆ squareCore ∪ F) :
    Stage3Case024.relativeUpperDensity A Set.univ = 0 := by
  let B : ℕ := hF.toFinset.card
  have hbound : ∀ n,
      (prefixCount (A ∩ Set.univ) n : ℝ) /
          (prefixCount (Set.univ : Language) n : ℝ) ≤
        ((Nat.sqrt n : ℝ) + 1 + B) / n := by
    intro n
    classical
    rw [prefixCount_univ]
    by_cases hn : n = 0
    · simp [hn]
    · apply div_le_div_of_nonneg_right
      · norm_cast
        calc
          prefixCount (A ∩ Set.univ) n = prefixCount A n := by simp
          _ ≤ prefixCount (squareCore ∪ F) n := prefixCount_mono hsub n
          _ ≤ prefixCount squareCore n + prefixCount F n := by
            classical
            unfold prefixCount prefixFinset
            apply (Finset.card_le_card ?_).trans (Finset.card_union_le _ _)
            intro x hx
            simp only [Finset.mem_filter, Finset.mem_range,
              Finset.mem_union, Set.mem_union] at hx ⊢
            rcases hx.2 with hxcore | hxF
            · exact Or.inl ⟨hx.1, hxcore⟩
            · exact Or.inr ⟨hx.1, hxF⟩
          _ ≤ (Nat.sqrt n + 1) + B := by
            gcongr
            · exact prefixCount_squareCore_le n
            · unfold prefixCount prefixFinset B
              apply Finset.card_le_card
              intro x hx
              rw [Set.Finite.mem_toFinset]
              exact (Finset.mem_filter.mp hx).2
      · positivity
  have hB : Tendsto (fun n : ℕ => (B : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have htendsto : Tendsto
      (fun n : ℕ => ((Nat.sqrt n : ℝ) + 1 + B) / n) atTop (𝓝 0) := by
    simpa only [add_div, zero_add] using tendsto_sparseSqrt_add_one_div.add hB
  have hratio : Tendsto
      (fun n : ℕ =>
        (prefixCount (A ∩ Set.univ) n : ℝ) /
          (prefixCount (Set.univ : Language) n : ℝ)) atTop (𝓝 0) := by
    apply squeeze_zero
      (fun n => div_nonneg (by positivity) (by positivity)) hbound htendsto
  exact hratio.limsup_eq

lemma generatorFirst_subset_range (input output : Stream) :
    GenLimit.GeneratorFirst input output ⊆ Set.range output := by
  rintro x ⟨t, ht, -⟩
  exact ⟨t, ht⟩

lemma eventual_core_gives_finite_cover {input output : Stream}
    (hvalid : GenLimit.NovelGeneratesInLimit input output squareCore) :
    ∃ F : Language, F.Finite ∧ Set.range output ⊆ squareCore ∪ F := by
  obtain ⟨T, hT⟩ := hvalid
  let F : Language := output '' Set.Iio T
  refine ⟨F, (Set.finite_Iio T).image output, ?_⟩
  rintro x ⟨t, rfl⟩
  by_cases ht : T ≤ t
  · exact Or.inl (hT t ht).1
  · exact Or.inr ⟨t, Nat.lt_of_not_ge ht, rfl⟩

lemma generatorFirst_density_univ_zero {input output : Stream}
    (hvalid : GenLimit.NovelGeneratesInLimit input output squareCore) :
    Stage3Case024.relativeUpperDensity
      (GenLimit.GeneratorFirst input output) Set.univ = 0 := by
  obtain ⟨F, hF, hcover⟩ := eventual_core_gives_finite_cover hvalid
  exact relativeUpperDensity_univ_eq_zero_of_subset_finite hF
    ((generatorFirst_subset_range input output).trans hcover)

end Stage3Case024Proof

namespace Stage3Case024Proof

open GenLimit
open GenLimit.InfiniteContamination
open GenLimit.PatientScope

/-- The first `i` canonical nonsquares. -/
def addedBefore (i : ℕ) : Language :=
  sparseBetweenSquares '' Set.Iio i

lemma addedBefore_mono {i j : ℕ} (hij : i ≤ j) :
    addedBefore i ⊆ addedBefore j := by
  rintro x ⟨k, hk, rfl⟩
  exact ⟨k, lt_of_lt_of_le hk hij, rfl⟩

lemma sparseBetweenSquares_mem_addedBefore {i j : ℕ} (hij : i < j) :
    sparseBetweenSquares i ∈ addedBefore j :=
  ⟨i, hij, rfl⟩

lemma sparseBetweenSquares_not_mem_addedBefore (i : ℕ) :
    sparseBetweenSquares i ∉ addedBefore i := by
  rintro ⟨k, hk, heq⟩
  have hki : k = i := sparseBetweenSquares_strictMono.injective heq
  subst k
  exact Nat.lt_irrefl i hk

/-- A strictly growing sparse chain, capped by the full universe. -/
def targetFamily (r : ℕ) (i : Fin r) : Language :=
  if (i : ℕ) = r - 1 then Set.univ else squareCore ∪ addedBefore i

lemma targetFamily_core_subset (r : ℕ) (i : Fin r) :
    squareCore ⊆ targetFamily r i := by
  intro x hx
  unfold targetFamily
  split
  · exact Set.mem_univ x
  · exact Or.inl hx

lemma targetFamily_infinite (r : ℕ) (i : Fin r) :
    (targetFamily r i).Infinite :=
  squareCore_infinite.mono (targetFamily_core_subset r i)

lemma targetFamily_strictlyNested {r : ℕ} (hr : 2 ≤ r) :
    Stage3Case024.StrictlyNested (targetFamily r) := by
  intro i j hij
  rw [Set.ssubset_iff_subset_ne]
  have hiLast : (i : ℕ) ≠ r - 1 := by omega
  constructor
  · intro x hx
    unfold targetFamily at hx ⊢
    simp only [hiLast, ↓reduceIte] at hx
    split
    · exact Set.mem_univ x
    · rcases hx with hxcore | hxadded
      · exact Or.inl hxcore
      · exact Or.inr (addedBefore_mono (Nat.le_of_lt hij) hxadded)
  · intro heq
    have hwNotI : sparseBetweenSquares i ∉ targetFamily r i := by
      simp only [targetFamily, hiLast, ↓reduceIte, Set.mem_union]
      push_neg
      exact ⟨sparseBetweenSquares_nonsquare i,
        sparseBetweenSquares_not_mem_addedBefore i⟩
    have hwJ : sparseBetweenSquares i ∈ targetFamily r j := by
      unfold targetFamily
      split
      · exact Set.mem_univ _
      · exact Or.inr (sparseBetweenSquares_mem_addedBefore hij)
    exact hwNotI (heq ▸ hwJ)

lemma targetFamily_legal (r : ℕ) (i : Fin r) :
    Stage3Case024.Legal commonInput (targetFamily r i) :=
  commonInput_legal _ (targetFamily_infinite r i) (targetFamily_core_subset r i)

/-- A generator whose output is a square larger than every current input and
whose square root increases every round. -/
def squareGenerator : Stage3Case024.OnlineGenerator :=
  fun t input _ =>
    let base := Finset.univ.sup input + t + 1
    base * base

noncomputable def squareOutput (input : Stream) : Stream :=
  fun t => squareGenerator t (fun i => input i) (fun _ => 0)

lemma squareOutput_follows (input : Stream) :
    Stage3Case024.Follows squareGenerator input (squareOutput input) := by
  intro t
  rfl

lemma input_le_prefixSup (input : Stream) {s t : ℕ} (hst : s ≤ t) :
    input s ≤ Finset.univ.sup (fun i : Fin (t + 1) => input i) := by
  let i : Fin (t + 1) := ⟨s, by omega⟩
  exact Finset.le_sup (f := fun i : Fin (t + 1) => input i)
    (show i ∈ (Finset.univ : Finset (Fin (t + 1))) by simp)

lemma prefixSup_mono (input : Stream) {s t : ℕ} (hst : s ≤ t) :
    Finset.univ.sup (fun i : Fin (s + 1) => input i) ≤
      Finset.univ.sup (fun i : Fin (t + 1) => input i) := by
  apply Finset.sup_le
  intro i hi
  exact input_le_prefixSup input (s := i) (t := t) (by omega)

lemma squareOutput_mem_core (input : Stream) (t : ℕ) :
    squareOutput input t ∈ squareCore := by
  unfold squareOutput squareGenerator squareCore
  simp only
  exact ⟨Finset.univ.sup (fun i : Fin (t + 1) => input i) + t + 1, rfl⟩

lemma squareOutput_fresh_input (input : Stream) (t : ℕ) :
    squareOutput input t ∉ GenLimit.sample input (t + 1) := by
  rw [GenLimit.mem_sample_iff]
  rintro ⟨s, hst, heq⟩
  have hle := input_le_prefixSup input (s := s) (t := t) (by omega)
  unfold squareOutput squareGenerator at heq
  dsimp at heq
  have hbase : 0 < Finset.univ.sup (fun i : Fin (t + 1) => input i) + t + 1 := by omega
  have hbig : input s <
      (Finset.univ.sup (fun i : Fin (t + 1) => input i) + t + 1) *
      (Finset.univ.sup (fun i : Fin (t + 1) => input i) + t + 1) := by
    nlinarith
  omega

lemma squareOutput_strictMono (input : Stream) : StrictMono (squareOutput input) := by
  intro s t hst
  have hsup := prefixSup_mono input (Nat.le_of_lt hst)
  unfold squareOutput squareGenerator
  dsimp
  apply Nat.mul_self_lt_mul_self
  omega

lemma squareOutput_novel (input : Stream) :
    GenLimit.NovelGeneratesInLimit input (squareOutput input) squareCore := by
  refine ⟨0, ?_⟩
  intro t ht
  refine ⟨squareOutput_mem_core input t, squareOutput_fresh_input input t, ?_⟩
  intro s hst
  exact ne_of_lt (squareOutput_strictMono input hst)

lemma targetFamily_globallyFeasible {r : ℕ} :
    Stage3Case024.GloballyFeasible (targetFamily r) := by
  refine ⟨squareGenerator, ?_⟩
  intro input hlegal
  refine ⟨squareOutput input, squareOutput_follows input, ?_⟩
  intro j
  obtain ⟨T, hT⟩ := squareOutput_novel input
  refine ⟨T, ?_⟩
  intro t ht
  obtain ⟨hcore, hfresh, hnovel⟩ := hT t ht
  exact ⟨targetFamily_core_subset r j hcore, hfresh, hnovel⟩

end Stage3Case024Proof
