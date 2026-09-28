import Stage3Model
import GenLimit.Paper17_InfiniteContamination.SharedVanishingPresentation
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open Filter MeasureTheory
open scoped Topology

namespace Stage3Case024Proof

open GenLimit.InfiniteContamination

noncomputable local instance : DecidablePred SparseSquare := Classical.decPred _
noncomputable local instance : DecidablePred SparseNonSquare := Classical.decPred _

def squareLanguage : Set ℕ := {n | SparseSquare n}

def nonsquareLanguage : Set ℕ := {n | SparseNonSquare n}

theorem squareLanguage_infinite : squareLanguage.Infinite := by
  have hmono : StrictMono (fun n : ℕ => n * n) := by
    apply strictMono_nat_of_lt_succ
    intro n
    nlinarith
  exact (Set.infinite_range_of_injective hmono.injective).mono (by
    rintro _ ⟨n, rfl⟩
    exact sparseSquare_mul_self n)

theorem nonsquareLanguage_infinite : nonsquareLanguage.Infinite :=
  sparseNonSquare_infinite

theorem square_disjoint_nonsquare :
    Disjoint squareLanguage nonsquareLanguage := by
  rw [Set.disjoint_left]
  intro n hnSquare hnNonsquare
  exact hnNonsquare hnSquare

theorem square_union_nonsquare :
    squareLanguage ∪ nonsquareLanguage = Set.univ := by
  ext n
  simp only [Set.mem_union, Set.mem_univ, iff_true, squareLanguage,
    nonsquareLanguage, Set.mem_setOf_eq]
  exact Classical.em (SparseSquare n)

noncomputable def commonInput : Stage3Case024.Stream :=
  squareSparseMerge squareLanguage nonsquareLanguage
    squareLanguage_infinite nonsquareLanguage_infinite

theorem commonInput_injective : Function.Injective commonInput := by
  exact squareSparseMerge_injective squareLanguage_infinite
    nonsquareLanguage_infinite square_disjoint_nonsquare

theorem commonInput_range : Set.range commonInput = Set.univ := by
  rw [commonInput, range_squareSparseMerge squareLanguage_infinite
    nonsquareLanguage_infinite, square_union_nonsquare]

theorem commonInput_legal_square :
    Stage3Case024.Legal commonInput squareLanguage := by
  refine ⟨squareLanguage_infinite, commonInput_injective, ?_, ?_⟩
  · rw [GenLimit.InfiniteContamination.NoOmissions, commonInput_range]
    exact Set.subset_univ _
  · exact squareSparseMerge_vanishingNoise_of_core_subset
      squareLanguage_infinite nonsquareLanguage_infinite (Set.Subset.rfl)

theorem commonInput_legal_of_square_subset {K : Set ℕ}
    (hsK : squareLanguage ⊆ K) : Stage3Case024.Legal commonInput K := by
  refine ⟨squareLanguage_infinite.mono hsK, commonInput_injective, ?_, ?_⟩
  · rw [GenLimit.InfiniteContamination.NoOmissions, commonInput_range]
    exact Set.subset_univ _
  · exact squareSparseMerge_vanishingNoise_of_core_subset
      squareLanguage_infinite nonsquareLanguage_infinite hsK

theorem prefixCount_univ (n : ℕ) :
    GenLimit.PatientScope.prefixCount (Set.univ : Set ℕ) n = n := by
  classical
  simp [GenLimit.PatientScope.prefixCount,
    GenLimit.PatientScope.prefixFinset]

theorem prefixCount_mono {A B : Set ℕ} (hAB : A ⊆ B) (n : ℕ) :
    GenLimit.PatientScope.prefixCount A n ≤
      GenLimit.PatientScope.prefixCount B n := by
  classical
  unfold GenLimit.PatientScope.prefixCount
  apply Finset.card_le_card
  intro x hx
  have hx' := GenLimit.PatientScope.mem_prefixFinset.mp hx
  exact GenLimit.PatientScope.mem_prefixFinset.mpr ⟨hx'.1, hAB hx'.2⟩

theorem prefixCount_square (n : ℕ) :
    GenLimit.PatientScope.prefixCount squareLanguage n =
      Nat.count SparseSquare n := by
  classical
  rw [Nat.count_eq_card_filter_range]
  rfl

theorem prefixCount_range_lt_le (output : ℕ → ℕ) (T n : ℕ) :
    GenLimit.PatientScope.prefixCount
        ({x | ∃ t < T, output t = x} : Set ℕ) n ≤ T := by
  classical
  unfold GenLimit.PatientScope.prefixCount GenLimit.PatientScope.prefixFinset
  let f : Finset ℕ := (Finset.range T).image output
  apply le_trans (b := f.card)
  · apply Finset.card_le_card
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_range, Set.mem_setOf_eq] at hx
    obtain ⟨t, ht, htx⟩ := hx.2
    exact Finset.mem_image.mpr ⟨t, Finset.mem_range.mpr ht, htx⟩
  · simpa [f] using (Finset.card_image_le : f.card ≤ (Finset.range T).card)

theorem generatorFirst_subset_eventual_square
    {input output : Stage3Case024.Stream}
    (hvalid : GenLimit.NovelGeneratesInLimit input output squareLanguage) :
    ∃ T, GenLimit.GeneratorFirst input output ⊆
      squareLanguage ∪ {x | ∃ t < T, output t = x} := by
  obtain ⟨T, hT⟩ := hvalid
  refine ⟨T, ?_⟩
  intro x hx
  obtain ⟨t, htx, -⟩ := hx
  by_cases ht : T ≤ t
  · exact Set.mem_union_left _ (htx ▸ (hT t ht).1)
  · exact Set.mem_union_right _ ⟨t, Nat.lt_of_not_ge ht, htx⟩

theorem prefixCount_generatorFirst_le
    {input output : Stage3Case024.Stream}
    (hvalid : GenLimit.NovelGeneratesInLimit input output squareLanguage) :
    ∃ T, ∀ n,
      GenLimit.PatientScope.prefixCount
          (GenLimit.GeneratorFirst input output) n ≤
        Nat.count SparseSquare n + T := by
  obtain ⟨T, hsub⟩ := generatorFirst_subset_eventual_square hvalid
  refine ⟨T, fun n => ?_⟩
  calc
    GenLimit.PatientScope.prefixCount (GenLimit.GeneratorFirst input output) n
        ≤ GenLimit.PatientScope.prefixCount
            (squareLanguage ∪ {x | ∃ t < T, output t = x}) n :=
      prefixCount_mono hsub n
    _ ≤ GenLimit.PatientScope.prefixCount squareLanguage n +
          GenLimit.PatientScope.prefixCount
            ({x | ∃ t < T, output t = x} : Set ℕ) n := by
      classical
      unfold GenLimit.PatientScope.prefixCount
      let early : Set ℕ := {x | ∃ t < T, output t = x}
      have hprefix :
          GenLimit.PatientScope.prefixFinset (squareLanguage ∪ early) n ⊆
            GenLimit.PatientScope.prefixFinset squareLanguage n ∪
              GenLimit.PatientScope.prefixFinset early n := by
        intro x hx
        obtain ⟨hxn, hxmem⟩ := GenLimit.PatientScope.mem_prefixFinset.mp hx
        rcases hxmem with hx | hx
        · exact Finset.mem_union_left _
            (GenLimit.PatientScope.mem_prefixFinset.mpr ⟨hxn, hx⟩)
        · exact Finset.mem_union_right _
            (GenLimit.PatientScope.mem_prefixFinset.mpr ⟨hxn, hx⟩)
      exact (Finset.card_le_card hprefix).trans (Finset.card_union_le _ _)
    _ ≤ Nat.count SparseSquare n + T := by
      rw [prefixCount_square]
      exact Nat.add_le_add_left (prefixCount_range_lt_le output T n) _

theorem tendsto_square_bound_add (T : ℕ) :
    Tendsto (fun n : ℕ => (((Nat.sqrt n : ℝ) + 1) + T) / n)
      atTop (𝓝 0) := by
  have hT : Tendsto (fun n : ℕ => (T : ℝ) / n) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using
      (tendsto_const_nhds.mul tendsto_inverse_atTop_nhds_zero_nat)
  simpa [add_div, add_assoc] using tendsto_sparseSqrt_add_one_div.add hT

theorem relativeUpperDensity_univ_eq_zero
    {input output : Stage3Case024.Stream}
    (hvalid : GenLimit.NovelGeneratesInLimit input output squareLanguage) :
    Stage3Case024.relativeUpperDensity
      (GenLimit.GeneratorFirst input output) Set.univ = 0 := by
  obtain ⟨T, hbound⟩ := prefixCount_generatorFirst_le hvalid
  unfold Stage3Case024.relativeUpperDensity
  simp only [Set.inter_univ]
  apply Filter.Tendsto.limsup_eq
  apply squeeze_zero
    (g := fun n : ℕ => (((Nat.sqrt n : ℝ) + 1) + T) / n)
  · intro n
    positivity
  · intro n
    rw [prefixCount_univ]
    by_cases hn : n = 0
    · simp [hn]
    · apply div_le_div_of_nonneg_right
      · exact_mod_cast (hbound n |>.trans
          (Nat.add_le_add_right (count_sparseSquare_le_sqrt_add_one n) T))
      · positivity
  · exact tendsto_square_bound_add T

theorem relativeUpperDensity_nonneg (A K : Set ℕ) :
    0 ≤ Stage3Case024.relativeUpperDensity A K := by
  unfold Stage3Case024.relativeUpperDensity
  apply le_limsup_of_frequently_le
  · exact Frequently.of_forall (fun n => by positivity)
  · exact isBoundedUnder_of ⟨1, fun n => by
      by_cases hden : GenLimit.PatientScope.prefixCount K n = 0
      · simp [hden]
      · rw [div_le_one (by positivity)]
        exact_mod_cast prefixCount_mono Set.inter_subset_right n⟩

theorem relativeUpperDensity_le_one (A K : Set ℕ) :
    Stage3Case024.relativeUpperDensity A K ≤ 1 := by
  unfold Stage3Case024.relativeUpperDensity
  apply limsup_le_of_le
  · exact isCoboundedUnder_le_of_le atTop (fun n => by positivity)
  · exact Eventually.of_forall (fun n => by
      by_cases hden : GenLimit.PatientScope.prefixCount K n = 0
      · simp [hden]
      · rw [div_le_one (by positivity)]
        exact_mod_cast prefixCount_mono Set.inter_subset_right n)

end Stage3Case024Proof

namespace Stage3Case024Proof

open GenLimit.InfiniteContamination

 theorem square_ssubset_univ : squareLanguage ⊂ (Set.univ : Set ℕ) := by
  rw [Set.ssubset_iff_subset_ne]
  refine ⟨Set.subset_univ _, ?_⟩
  intro heq
  have htwo : 2 ∈ squareLanguage := heq ▸ Set.mem_univ 2
  rcases htwo with ⟨k, hk⟩
  by_cases hklt : k < 2
  · interval_cases k <;> norm_num at hk
  · have hkge : 2 ≤ k := Nat.le_of_not_gt hklt
    have hmul := Nat.mul_le_mul hkge hkge
    omega

 theorem pairObstruction :
    Stage3Case024.PairObstruction squareLanguage Set.univ commonInput := by
  intro Ω _ μ _ gen output _ _ hIntSquare _ hValidSquare _
  have hzeroAE :
      (fun ω => Stage3Case024.relativeUpperDensity
        (GenLimit.GeneratorFirst commonInput (output ω)) Set.univ) =ᵐ[μ]
        (fun _ => 0) := by
    exact hValidSquare.mono (fun ω hω =>
      relativeUpperDensity_univ_eq_zero hω)
  have hExpectedUniv :
      Stage3Case024.expectedUpperDensity μ Set.univ commonInput output = 0 := by
    unfold Stage3Case024.expectedUpperDensity
    rw [integral_congr_ae hzeroAE]
    simp
  have hSquareLe :
      Stage3Case024.expectedUpperDensity μ squareLanguage commonInput output ≤ 1 := by
    unfold Stage3Case024.expectedUpperDensity
    calc
      (∫ ω, Stage3Case024.relativeUpperDensity
          (GenLimit.GeneratorFirst commonInput (output ω)) squareLanguage ∂μ)
          ≤ ∫ _ : Ω, (1 : ℝ) ∂μ := by
            apply integral_mono_ae hIntSquare (integrable_const 1)
            exact ae_of_all μ (fun ω => relativeUpperDensity_le_one _ _)
      _ = 1 := by simp [integral_const]
  constructor
  · rw [hExpectedUniv, add_zero]
    exact hSquareLe
  · intro hboth
    rw [hExpectedUniv] at hboth
    linarith

end Stage3Case024Proof

namespace Stage3Case024Proof

open GenLimit.InfiniteContamination

noncomputable local instance : DecidablePred SparseSquare := Classical.decPred _
noncomputable local instance : DecidablePred SparseNonSquare := Classical.decPred _

noncomputable def nonsquarePrefix (j : ℕ) : Set ℕ :=
  {x | SparseNonSquare x ∧ Nat.count SparseNonSquare x < j}

noncomputable def nestedFamily (r : ℕ) (j : Fin r) : Set ℕ :=
  if j.val + 1 = r then Set.univ else squareLanguage ∪ nonsquarePrefix j.val

theorem square_subset_nestedFamily (r : ℕ) (j : Fin r) :
    squareLanguage ⊆ nestedFamily r j := by
  intro x hx
  unfold nestedFamily
  split
  · exact Set.mem_univ x
  · exact Set.mem_union_left _ hx

theorem nestedFamily_last {r : ℕ} (hr : 0 < r) :
    nestedFamily r ⟨r - 1, Nat.sub_lt hr Nat.zero_lt_one⟩ = Set.univ := by
  unfold nestedFamily
  apply if_pos
  change r - 1 + 1 = r
  omega

theorem nonsquare_nth_mem (j : ℕ) :
    SparseNonSquare (Nat.nth SparseNonSquare j) :=
  Nat.nth_mem_of_infinite nonsquareLanguage_infinite j

theorem nonsquare_count_nth (j : ℕ) :
    Nat.count SparseNonSquare (Nat.nth SparseNonSquare j) = j :=
  Nat.count_nth_of_infinite nonsquareLanguage_infinite j

theorem nestedFamily_strict {r : ℕ} (hr : 2 ≤ r) :
    Stage3Case024.StrictlyNested (nestedFamily r) := by
  intro i j hij
  have hiNotLast : i.val + 1 ≠ r := by omega
  by_cases hjLast : j.val + 1 = r
  · change (if i.val + 1 = r then Set.univ else
        squareLanguage ∪ nonsquarePrefix i.val) ⊂
      (if j.val + 1 = r then Set.univ else
        squareLanguage ∪ nonsquarePrefix j.val)
    rw [if_neg hiNotLast, if_pos hjLast, Set.ssubset_iff_subset_ne]
    refine ⟨Set.subset_univ _, ?_⟩
    intro heq
    let x := Nat.nth SparseNonSquare i.val
    have hxuniv : x ∈ (Set.univ : Set ℕ) := Set.mem_univ x
    have hxi : x ∈ squareLanguage ∪ nonsquarePrefix i.val := by
      rw [heq]
      exact hxuniv
    rcases hxi with hxsquare | hxprefix
    · exact (nonsquare_nth_mem i.val) hxsquare
    · change SparseNonSquare (Nat.nth SparseNonSquare i.val) ∧
          Nat.count SparseNonSquare (Nat.nth SparseNonSquare i.val) < i.val at hxprefix
      rw [nonsquare_count_nth] at hxprefix
      exact (Nat.lt_irrefl i.val) hxprefix.2
  · change (if i.val + 1 = r then Set.univ else
        squareLanguage ∪ nonsquarePrefix i.val) ⊂
      (if j.val + 1 = r then Set.univ else
        squareLanguage ∪ nonsquarePrefix j.val)
    rw [if_neg hiNotLast, if_neg hjLast, Set.ssubset_iff_subset_ne]
    constructor
    · intro x hx
      rcases hx with hxsquare | hxprefix
      · exact Set.mem_union_left _ hxsquare
      · exact Set.mem_union_right _ ⟨hxprefix.1,
          lt_trans hxprefix.2 hij⟩
    · intro heq
      let x := Nat.nth SparseNonSquare i.val
      have hxj : x ∈ squareLanguage ∪ nonsquarePrefix j.val := by
        apply Set.mem_union_right
        refine ⟨nonsquare_nth_mem i.val, ?_⟩
        dsimp [nonsquarePrefix, x]
        rw [nonsquare_count_nth]
        exact hij
      have hxi : x ∈ squareLanguage ∪ nonsquarePrefix i.val := heq ▸ hxj
      rcases hxi with hxsquare | hxprefix
      · exact (nonsquare_nth_mem i.val) hxsquare
      · change SparseNonSquare (Nat.nth SparseNonSquare i.val) ∧
            Nat.count SparseNonSquare (Nat.nth SparseNonSquare i.val) < i.val at hxprefix
        rw [nonsquare_count_nth] at hxprefix
        exact (Nat.lt_irrefl i.val) hxprefix.2

noncomputable def historySup {n : ℕ} (history : Fin n → ℕ) : ℕ :=
  Finset.univ.sup history

noncomputable def freshSquareGenerator : Stage3Case024.OnlineGenerator :=
  fun t input _ =>
    let base := historySup input + t + 1
    base * base

noncomputable def generatedOutput (input : Stage3Case024.Stream) :
    Stage3Case024.Stream :=
  fun t => freshSquareGenerator t (fun i => input i) (fun _ => 0)

theorem historySup_le_of_prefix {s t : ℕ} (hst : s ≤ t)
    (input : Stage3Case024.Stream) :
    historySup (fun i : Fin (s + 1) => input i) ≤
      historySup (fun i : Fin (t + 1) => input i) := by
  unfold historySup
  apply Finset.sup_le
  intro i _
  let j : Fin (t + 1) := ⟨i.val, lt_of_lt_of_le i.isLt (Nat.succ_le_succ hst)⟩
  exact Finset.le_sup (s := Finset.univ)
    (f := fun q : Fin (t + 1) => input q) (b := j) (Finset.mem_univ j)

theorem generatedOutput_follows (input : Stage3Case024.Stream) :
    Stage3Case024.Follows freshSquareGenerator input (generatedOutput input) := by
  intro t
  rfl

theorem generatedOutput_novel (input : Stage3Case024.Stream) :
    GenLimit.NovelGeneratesInLimit input (generatedOutput input) squareLanguage := by
  refine ⟨0, fun t _ => ?_⟩
  let base := historySup (fun i : Fin (t + 1) => input i) + t + 1
  have hbase : 0 < base := by simp [base]
  have hout : generatedOutput input t = base * base := by rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [hout]
    exact sparseSquare_mul_self base
  · rw [GenLimit.mem_sample_iff]
    rintro ⟨s, hst, hs⟩
    have hsle : input s ≤ historySup (fun i : Fin (t + 1) => input i) := by
      exact Finset.le_sup (s := Finset.univ)
        (f := fun i : Fin (t + 1) => input i)
        (b := ⟨s, hst⟩) (Finset.mem_univ _)
    rw [hout] at hs
    have hlt : input s < base * base := by
      have : historySup (fun i : Fin (t + 1) => input i) < base := by
        dsimp [base]
        omega
      nlinarith
    omega
  · intro s hst hEq
    let baseS := historySup (fun i : Fin (s + 1) => input i) + s + 1
    have hsup := historySup_le_of_prefix (Nat.le_of_lt hst) input
    have hbaseLt : baseS < base := by
      dsimp [baseS, base]
      omega
    have hsqLt : baseS * baseS < base * base := by
      nlinarith [show 0 < baseS by simp [baseS]]
    change baseS * baseS = base * base at hEq
    omega

theorem globallyFeasible_nestedFamily {r : ℕ} :
    Stage3Case024.GloballyFeasible (nestedFamily r) := by
  refine ⟨freshSquareGenerator, fun input _ =>
    ⟨generatedOutput input, generatedOutput_follows input, ?_⟩⟩
  intro j
  obtain ⟨T, hT⟩ := generatedOutput_novel input
  refine ⟨T, fun t ht => ?_⟩
  obtain ⟨hmem, hfresh, hnovel⟩ := hT t ht
  exact ⟨square_subset_nestedFamily r j hmem, hfresh, hnovel⟩

end Stage3Case024Proof

namespace Stage3Case024Proof

open GenLimit.InfiniteContamination

noncomputable local instance : DecidablePred SparseSquare := Classical.decPred _
noncomputable local instance : DecidablePred SparseNonSquare := Classical.decPred _

theorem nonsquarePrefix_zero : nonsquarePrefix 0 = ∅ := by
  ext x
  simp [nonsquarePrefix]

theorem nestedFamily_zero {r : ℕ} (hr : 2 ≤ r) :
    nestedFamily r ⟨0, lt_of_lt_of_le (by omega) hr⟩ = squareLanguage := by
  change (if 0 + 1 = r then Set.univ else
    squareLanguage ∪ nonsquarePrefix 0) = squareLanguage
  rw [if_neg (by omega), nonsquarePrefix_zero, Set.union_empty]

theorem manyTargetObstruction {r : ℕ} (hr : 2 ≤ r) :
    Stage3Case024.ManyTargetObstruction (nestedFamily r) commonInput := by
  intro Ω _ μ _ gen output _ _ _ hValid
  let zero : Fin r := ⟨0, lt_of_lt_of_le (by omega) hr⟩
  let last : Fin r := ⟨r - 1, Nat.sub_lt (by omega) Nat.zero_lt_one⟩
  have hValidSquare : Stage3Case024.EventuallyFreshValid μ squareLanguage
      commonInput output := by
    have hz := hValid zero
    rw [show nestedFamily r zero = squareLanguage by
      simpa [zero] using nestedFamily_zero hr] at hz
    exact hz
  have hzeroAE :
      (fun ω => Stage3Case024.relativeUpperDensity
        (GenLimit.GeneratorFirst commonInput (output ω)) Set.univ) =ᵐ[μ]
        (fun _ => 0) := by
    exact hValidSquare.mono (fun ω hω =>
      relativeUpperDensity_univ_eq_zero hω)
  refine ⟨last, ?_⟩
  have hlast : nestedFamily r last = Set.univ := by
    simpa [last] using nestedFamily_last (show 0 < r by omega)
  rw [hlast]
  unfold Stage3Case024.expectedUpperDensity
  rw [integral_congr_ae hzeroAE]
  simp

theorem manyTargetWitness {r : ℕ} (hr : 2 ≤ r) :
    Stage3Case024.ManyTargetWitness (nestedFamily r) commonInput := by
  refine ⟨nestedFamily_strict hr, ?_, globallyFeasible_nestedFamily,
    manyTargetObstruction hr⟩
  intro j
  exact commonInput_legal_of_square_subset (square_subset_nestedFamily r j)

end Stage3Case024Proof
