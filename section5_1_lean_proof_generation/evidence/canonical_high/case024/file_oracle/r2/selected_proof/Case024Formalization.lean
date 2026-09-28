import Stage3Model
import GenLimit.Paper17_InfiniteContamination.SharedVanishingPresentation

open Filter MeasureTheory
open scoped Topology BigOperators

namespace Case024

noncomputable abbrev pc := GenLimit.PatientScope.prefixCount
noncomputable abbrev pf := GenLimit.PatientScope.prefixFinset

def squareSet : Set ℕ := {n | GenLimit.InfiniteContamination.SparseSquare n}

noncomputable local instance :
    DecidablePred GenLimit.InfiniteContamination.SparseSquare := Classical.decPred _

example (n : ℕ) : pc Set.univ n = n := by
  simp [pc, GenLimit.PatientScope.prefixCount, GenLimit.PatientScope.prefixFinset]

example (n : ℕ) : pc squareSet n = Nat.count GenLimit.InfiniteContamination.SparseSquare n := by
  classical
  rw [Nat.count_eq_card_filter_range]
  rfl

lemma pc_mono {A B : Set ℕ} (h : A ⊆ B) (n : ℕ) : pc A n ≤ pc B n := by
  classical
  unfold pc GenLimit.PatientScope.prefixCount GenLimit.PatientScope.prefixFinset
  apply Finset.card_le_card
  intro x hx
  simp only [Finset.mem_filter, Finset.mem_range] at hx ⊢
  exact ⟨hx.1, h hx.2⟩

lemma pc_union_le (A B : Set ℕ) (n : ℕ) : pc (A ∪ B) n ≤ pc A n + pc B n := by
  classical
  unfold pc GenLimit.PatientScope.prefixCount GenLimit.PatientScope.prefixFinset
  simp only [Set.mem_union]
  let a := (Finset.range n).filter fun x => x ∈ A
  let b := (Finset.range n).filter fun x => x ∈ B
  calc
    ((Finset.range n).filter fun x => x ∈ A ∨ x ∈ B).card = (a ∪ b).card := by
      congr 1
      ext x
      simp [a, b, and_or_left]
    _ ≤ a.card + b.card := Finset.card_union_le a b
    _ = _ := rfl

lemma pc_range_fin_le (output : ℕ → ℕ) (T n : ℕ) :
    pc (output '' Set.Iio T) n ≤ T := by
  classical
  unfold pc GenLimit.PatientScope.prefixCount GenLimit.PatientScope.prefixFinset
  calc
    ((Finset.range n).filter fun x => x ∈ output '' Set.Iio T).card ≤
        ((Finset.range T).image output).card := by
      apply Finset.card_le_card
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_range, Set.mem_image, Set.mem_Iio] at hx
      obtain ⟨-, y, hy, rfl⟩ := hx
      exact Finset.mem_image.mpr ⟨y, Finset.mem_range.mpr hy, rfl⟩
    _ ≤ (Finset.range T).card := Finset.card_image_le
    _ = T := Finset.card_range T

lemma generatorFirst_subset_core_union_early
    {input output : ℕ → ℕ} {T : ℕ}
    (hT : ∀ t, T ≤ t → output t ∈ squareSet) :
    GenLimit.GeneratorFirst input output ⊆ squareSet ∪ output '' Set.Iio T := by
  intro x hx
  obtain ⟨t, rfl, -⟩ := hx
  by_cases ht : T ≤ t
  · exact Or.inl (hT t ht)
  · exact Or.inr ⟨t, Nat.lt_of_not_ge ht, rfl⟩

lemma density_seq_tendsto_zero
    {input output : ℕ → ℕ}
    (hvalid : GenLimit.NovelGeneratesInLimit input output squareSet) :
    Tendsto
      (fun n : ℕ =>
        (pc (GenLimit.GeneratorFirst input output ∩ Set.univ) n : ℝ) /
          (pc Set.univ n : ℝ))
      atTop (𝓝 0) := by
  obtain ⟨T, hT⟩ := hvalid
  have hsub : GenLimit.GeneratorFirst input output ⊆
      squareSet ∪ output '' Set.Iio T :=
    generatorFirst_subset_core_union_early (fun t ht => (hT t ht).1)
  have hboundNat (n : ℕ) :
      pc (GenLimit.GeneratorFirst input output ∩ Set.univ) n ≤
        Nat.sqrt n + 1 + T := by
    calc
      pc (GenLimit.GeneratorFirst input output ∩ Set.univ) n =
          pc (GenLimit.GeneratorFirst input output) n := by simp
      _ ≤ pc (squareSet ∪ output '' Set.Iio T) n := pc_mono hsub n
      _ ≤ pc squareSet n + pc (output '' Set.Iio T) n := pc_union_le _ _ n
      _ ≤ (Nat.sqrt n + 1) + T := Nat.add_le_add
        (by
          classical
          rw [show pc squareSet n = Nat.count GenLimit.InfiniteContamination.SparseSquare n by
            classical
            rw [Nat.count_eq_card_filter_range]
            rfl]
          exact GenLimit.InfiniteContamination.count_sparseSquare_le_sqrt_add_one n)
        (pc_range_fin_le output T n)
  have hupper : Tendsto
      (fun n : ℕ => (((Nat.sqrt n : ℝ) + 1) + T) / (n : ℝ))
      atTop (𝓝 0) := by
    simpa [add_div] using
      GenLimit.InfiniteContamination.tendsto_sparseSqrt_add_one_div.add
        (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop :
          Tendsto (fun n : ℕ => (T : ℝ) / (n : ℝ)) atTop (𝓝 0))
  apply squeeze_zero' (g := fun n : ℕ => (((Nat.sqrt n : ℝ) + 1) + T) / (n : ℝ))
  · exact Eventually.of_forall fun n => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    simp only [pc, GenLimit.PatientScope.prefixCount,
      GenLimit.PatientScope.prefixFinset, Set.mem_univ, and_true,
      Finset.filter_true, Finset.card_range]
    apply (div_le_div_iff_of_pos_right hnpos).2
    exact_mod_cast hboundNat n
  · exact hupper

lemma relativeUpperDensity_univ_zero
    {input output : ℕ → ℕ}
    (hvalid : GenLimit.NovelGeneratesInLimit input output squareSet) :
    Stage3Case024.relativeUpperDensity
      (GenLimit.GeneratorFirst input output) Set.univ = 0 := by
  unfold Stage3Case024.relativeUpperDensity
  exact (density_seq_tendsto_zero hvalid).limsup_eq

end Case024

namespace Case024

lemma relativeUpperDensity_le_one (A K : Set ℕ) :
    Stage3Case024.relativeUpperDensity A K ≤ 1 := by
  unfold Stage3Case024.relativeUpperDensity
  apply limsup_le_of_le
  · exact isCoboundedUnder_le_of_le atTop fun n =>
      div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · exact Eventually.of_forall fun n => by
      by_cases hzero : pc K n = 0
      · have hnum : pc (A ∩ K) n = 0 :=
          Nat.eq_zero_of_le_zero (pc_mono Set.inter_subset_right n |>.trans_eq hzero)
        simp [hzero, hnum]
      · apply (div_le_one (by positivity)).2
        exact_mod_cast pc_mono Set.inter_subset_right n

lemma pairObstruction_square_univ (input : ℕ → ℕ) :
    Stage3Case024.PairObstruction squareSet Set.univ input := by
  intro Ω _ μ _ gen output _ _ hint0 _ hev0 _
  have haeZero : ∀ᵐ ω ∂μ,
      Stage3Case024.relativeUpperDensity
        (GenLimit.GeneratorFirst input (output ω)) Set.univ = 0 :=
    hev0.mono fun ω hω => relativeUpperDensity_univ_zero hω
  have hExpectedUniv :
      Stage3Case024.expectedUpperDensity μ Set.univ input output = 0 := by
    unfold Stage3Case024.expectedUpperDensity
    rw [integral_congr_ae haeZero]
    simp
  have hExpectedCore :
      Stage3Case024.expectedUpperDensity μ squareSet input output ≤ 1 := by
    unfold Stage3Case024.expectedUpperDensity
    calc
      (∫ ω, Stage3Case024.relativeUpperDensity
          (GenLimit.GeneratorFirst input (output ω)) squareSet ∂μ) ≤
          ∫ _ : Ω, (1 : ℝ) ∂μ := by
        apply integral_mono hint0
        · exact integrable_const 1
        · exact fun ω => relativeUpperDensity_le_one _ _
      _ = 1 := by simp
  constructor
  · rw [hExpectedUniv]
    linarith
  · rw [hExpectedUniv]
    norm_num

end Case024

namespace Case024

lemma squareSet_infinite : squareSet.Infinite := by
  have hmono : StrictMono (fun k : ℕ => k * k) := by
    apply strictMono_nat_of_lt_succ
    intro k
    nlinarith
  apply (Set.infinite_range_of_injective hmono.injective).mono
  rintro _ ⟨k, rfl⟩
  exact GenLimit.InfiniteContamination.sparseSquare_mul_self k

noncomputable def commonInput : Stage3Case024.Stream :=
  GenLimit.InfiniteContamination.sparseMergePresentation
    squareSet (Set.univ \ squareSet) squareSet_infinite

lemma commonInput_injective : Function.Injective commonInput := by
  apply GenLimit.InfiniteContamination.sparseMergePresentation_injective
    squareSet_infinite
  exact Set.disjoint_sdiff_right

lemma commonInput_range : Set.range commonInput = Set.univ := by
  rw [commonInput,
    GenLimit.InfiniteContamination.range_sparseMergePresentation squareSet_infinite]
  simp

lemma commonInput_legal {K : Set ℕ} (hKinf : K.Infinite)
    (hcore : squareSet ⊆ K) : Stage3Case024.Legal commonInput K := by
  refine ⟨hKinf, commonInput_injective, ?_, ?_⟩
  · intro x hx
    rw [commonInput_range]
    trivial
  · exact
      GenLimit.InfiniteContamination.sparseMergePresentation_vanishingNoise_of_core_subset
        squareSet_infinite hcore

lemma squareSet_ssubset_univ : squareSet ⊂ Set.univ := by
  refine ⟨Set.subset_univ _, ?_⟩
  intro h
  have hnonsquare := GenLimit.InfiniteContamination.sparseBetweenSquares_nonsquare 0
  exact hnonsquare (h (Set.mem_univ _))

lemma pairWitness :
    ∃ K₀ K₁ : Stage3Case024.Language, ∃ input : Stage3Case024.Stream,
      K₀ ⊂ K₁ ∧ Stage3Case024.Legal input K₀ ∧
        Stage3Case024.Legal input K₁ ∧
        Stage3Case024.PairObstruction K₀ K₁ input := by
  refine ⟨squareSet, Set.univ, commonInput, squareSet_ssubset_univ,
    commonInput_legal squareSet_infinite Set.Subset.rfl, ?_,
    pairObstruction_square_univ commonInput⟩
  exact commonInput_legal Set.infinite_univ (Set.subset_univ _)

end Case024

namespace Case024

abbrev exceptionalValue := GenLimit.InfiniteContamination.sparseBetweenSquares

def exceptionalPrefix (j : ℕ) : Set ℕ := exceptionalValue '' Set.Iio j

def targetFamily (r : ℕ) (j : Fin r) : Stage3Case024.Language :=
  if j.val + 1 = r then Set.univ else squareSet ∪ exceptionalPrefix j.val

lemma exceptionalValue_not_square (k : ℕ) : exceptionalValue k ∉ squareSet :=
  GenLimit.InfiniteContamination.sparseBetweenSquares_nonsquare k

lemma exceptionalValue_injective : Function.Injective exceptionalValue :=
  GenLimit.InfiniteContamination.sparseBetweenSquares_strictMono.injective

lemma exceptionalPrefix_mono {i j : ℕ} (hij : i ≤ j) :
    exceptionalPrefix i ⊆ exceptionalPrefix j := by
  rintro x ⟨k, hk, rfl⟩
  exact ⟨k, lt_of_lt_of_le hk hij, rfl⟩

lemma exceptionalValue_mem_prefix {i j : ℕ} (hij : i < j) :
    exceptionalValue i ∈ exceptionalPrefix j := ⟨i, hij, rfl⟩

lemma exceptionalValue_not_mem_own_prefix (i : ℕ) :
    exceptionalValue i ∉ exceptionalPrefix i := by
  rintro ⟨k, hk, heq⟩
  have hk' : k < i := hk
  have hki : k = i := exceptionalValue_injective heq
  omega

lemma targetFamily_core_subset (r : ℕ) (j : Fin r) :
    squareSet ⊆ targetFamily r j := by
  intro x hx
  unfold targetFamily
  split <;> simp_all

lemma targetFamily_infinite (r : ℕ) (j : Fin r) :
    (targetFamily r j).Infinite :=
  squareSet_infinite.mono (targetFamily_core_subset r j)

lemma targetFamily_strictlyNested {r : ℕ} (hr : 2 ≤ r) :
    Stage3Case024.StrictlyNested (targetFamily r) := by
  intro i j hij
  have hij' : i.val < j.val := hij
  unfold targetFamily
  split_ifs with hi hj
  · omega
  · exact (hj (by omega)).elim
  · refine ⟨?_, ?_⟩
    · exact Set.subset_univ _
    · intro heq
      have hmem : exceptionalValue j.val ∈
          squareSet ∪ exceptionalPrefix i.val := heq (Set.mem_univ _)
      rcases hmem with hsquare | hprefix
      · exact exceptionalValue_not_square j.val hsquare
      · obtain ⟨k, hk, heqk⟩ := hprefix
        have hk' : k < i.val := hk
        have hkj : k = j.val := exceptionalValue_injective heqk
        omega
  · refine ⟨?_, ?_⟩
    · intro x hx
      rcases hx with hsquare | hprefix
      · exact Or.inl hsquare
      · exact Or.inr (exceptionalPrefix_mono (Nat.le_of_lt hij') hprefix)
    · intro heq
      have hmem : exceptionalValue i.val ∈
          squareSet ∪ exceptionalPrefix i.val :=
        heq (Or.inr (exceptionalValue_mem_prefix hij'))
      rcases hmem with hsquare | hprefix
      · exact exceptionalValue_not_square i.val hsquare
      · exact exceptionalValue_not_mem_own_prefix i.val hprefix

lemma targetFamily_last_univ {r : ℕ} (hr : 1 ≤ r) :
    targetFamily r ⟨r - 1, Nat.sub_lt (by omega) (by omega)⟩ = Set.univ := by
  simp [targetFamily]
  omega

lemma targetFamily_zero_core {r : ℕ} (hr : 2 ≤ r) :
    targetFamily r ⟨0, by omega⟩ = squareSet := by
  simp [targetFamily, exceptionalPrefix]
  omega

lemma targetFamily_legal (r : ℕ) (j : Fin r) :
    Stage3Case024.Legal commonInput (targetFamily r j) :=
  commonInput_legal (targetFamily_infinite r j) (targetFamily_core_subset r j)

end Case024

namespace Case024

noncomputable def coreGenerator : Stage3Case024.OnlineGenerator :=
  fun t inputHistory _ =>
    let mass := ∑ i : Fin (t + 1), (inputHistory i + 1)
    mass * mass

noncomputable def inputMass (input : Stage3Case024.Stream) (t : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (t + 1), (input i + 1)

noncomputable def coreOutput (input : Stage3Case024.Stream) : Stage3Case024.Stream :=
  fun t =>
    let mass := inputMass input t
    mass * mass

lemma inputMass_pos (input : Stage3Case024.Stream) (t : ℕ) :
    0 < inputMass input t := by
  simp only [inputMass, Finset.sum_range_succ]
  omega

lemma input_lt_inputMass (input : Stage3Case024.Stream) {s t : ℕ} (hst : s < t + 1) :
    input s < inputMass input t := by
  unfold inputMass
  have hterm : input s + 1 ≤ ∑ i ∈ Finset.range (t + 1), (input i + 1) := by
    apply Finset.single_le_sum (fun i _ => Nat.zero_le (input i + 1))
    exact Finset.mem_range.mpr hst
  omega

lemma inputMass_strictMono (input : Stage3Case024.Stream) :
    StrictMono (inputMass input) := by
  apply strictMono_nat_of_lt_succ
  intro t
  simp only [inputMass, Finset.sum_range_succ]
  omega

lemma coreOutput_eq (input : Stage3Case024.Stream) (t : ℕ) :
    coreOutput input t = inputMass input t * inputMass input t := rfl

lemma coreOutput_follows (input : Stage3Case024.Stream) :
    Stage3Case024.Follows coreGenerator input (coreOutput input) := by
  intro t
  change inputMass input t * inputMass input t =
    (∑ i : Fin (t + 1), (input i + 1)) *
      ∑ i : Fin (t + 1), (input i + 1)
  have hmass : (∑ i : Fin (t + 1), (input i + 1)) = inputMass input t := by
    exact Fin.sum_univ_eq_sum_range (fun i => input i + 1) (t + 1)
  rw [hmass]

lemma coreOutput_novel (input : Stage3Case024.Stream) :
    GenLimit.NovelGeneratesInLimit input (coreOutput input) squareSet := by
  refine ⟨0, ?_⟩
  intro t _
  refine ⟨?_, ?_, ?_⟩
  · rw [coreOutput_eq]
    exact GenLimit.InfiniteContamination.sparseSquare_mul_self _
  · intro hsample
    rw [GenLimit.mem_sample_iff] at hsample
    obtain ⟨s, hst, hs⟩ := hsample
    have hlt : input s < inputMass input t := input_lt_inputMass input hst
    have hmassLe : inputMass input t ≤ inputMass input t * inputMass input t := by
      nlinarith [inputMass_pos input t]
    rw [coreOutput_eq] at hs
    omega
  · intro s hst heq
    rw [coreOutput_eq, coreOutput_eq] at heq
    have hmass : inputMass input s < inputMass input t := inputMass_strictMono input hst
    nlinarith [inputMass_pos input s, inputMass_pos input t]

lemma targetFamily_globallyFeasible {r : ℕ} (hr : 2 ≤ r) :
    Stage3Case024.GloballyFeasible (targetFamily r) := by
  refine ⟨coreGenerator, ?_⟩
  intro input _
  refine ⟨coreOutput input, coreOutput_follows input, ?_⟩
  intro j
  obtain ⟨T, hT⟩ := coreOutput_novel input
  refine ⟨T, ?_⟩
  intro t ht
  obtain ⟨hcore, hfresh, hnovel⟩ := hT t ht
  exact ⟨targetFamily_core_subset r j hcore, hfresh, hnovel⟩

end Case024

namespace Case024

lemma targetFamily_manyTargetObstruction {r : ℕ} (hr : 2 ≤ r) :
    Stage3Case024.ManyTargetObstruction (targetFamily r) commonInput := by
  intro Ω _ μ _ gen output _ _ _ hvalid
  let first : Fin r := ⟨0, by omega⟩
  let last : Fin r := ⟨r - 1, Nat.sub_lt (by omega) (by omega)⟩
  have hfirst : targetFamily r first = squareSet := by
    exact targetFamily_zero_core hr
  have hlast : targetFamily r last = Set.univ := by
    exact targetFamily_last_univ (by omega)
  have haeZero : ∀ᵐ ω ∂μ,
      Stage3Case024.relativeUpperDensity
        (GenLimit.GeneratorFirst commonInput (output ω)) Set.univ = 0 :=
    (hvalid first).mono fun ω hω =>
      relativeUpperDensity_univ_zero (by simpa [hfirst] using hω)
  refine ⟨last, ?_⟩
  rw [hlast]
  unfold Stage3Case024.expectedUpperDensity
  rw [integral_congr_ae haeZero]
  simp

lemma targetFamily_manyTargetWitness {r : ℕ} (hr : 2 ≤ r) :
    Stage3Case024.ManyTargetWitness (targetFamily r) commonInput := by
  exact ⟨targetFamily_strictlyNested hr, targetFamily_legal r,
    targetFamily_globallyFeasible hr, targetFamily_manyTargetObstruction hr⟩

end Case024

theorem stage3_result : Stage3Case024.MainClaim := by
  refine ⟨Case024.pairWitness, ?_⟩
  intro r hr
  exact ⟨Case024.targetFamily r, Case024.commonInput,
    Case024.targetFamily_manyTargetWitness hr⟩
