import Stage3Model
import GenLimit.Paper17_InfiniteContamination.SharedVanishingPresentation
import GenLimit.Paper39_DenseGeneration.Abstract.TargetDensity
import GenLimit.Support.Fresh

open Filter MeasureTheory
open scoped Topology

namespace Case024Proof

open Stage3Case024
open GenLimit.InfiniteContamination
open GenLimit.PatientScope

noncomputable section

def core : Set ℕ := {n | SparseSquare n}

def exceptional : Set ℕ := coreᶜ

theorem core_infinite : core.Infinite := by
  let f : ℕ → ℕ := fun k => k * k
  have hmono : StrictMono f := by
    apply strictMono_nat_of_lt_succ
    intro k
    dsimp [f]
    nlinarith
  have hf : Function.Injective f := hmono.injective
  exact (Set.infinite_range_of_injective hf).mono (by
    rintro _ ⟨k, rfl⟩
    exact ⟨k, rfl⟩)

theorem exceptional_infinite : exceptional.Infinite := by
  exact sparseNonSquare_infinite

def commonInput : Stream :=
  squareSparseMerge core exceptional core_infinite exceptional_infinite

theorem commonInput_injective : Function.Injective commonInput := by
  apply squareSparseMerge_injective core_infinite exceptional_infinite
  exact Set.disjoint_left.mpr (fun x hx hxcomp => hxcomp hx)

theorem commonInput_range : Set.range commonInput = Set.univ := by
  rw [commonInput, range_squareSparseMerge core_infinite exceptional_infinite]
  exact Set.union_compl_self core

theorem legal_of_core_subset {K : Language} (hcore : core ⊆ K) :
    Legal commonInput K := by
  refine ⟨core_infinite.mono hcore, commonInput_injective, ?_, ?_⟩
  · rw [GenLimit.InfiniteContamination.NoOmissions, commonInput_range]
    exact Set.subset_univ K
  · exact squareSparseMerge_vanishingNoise_of_core_subset
      core_infinite exceptional_infinite hcore

theorem prefixCount_univ (n : ℕ) : prefixCount (Set.univ : Set ℕ) n = n := by
  simp [prefixCount, prefixFinset]

theorem prefixCount_core_le (n : ℕ) :
    prefixCount core n ≤ Nat.sqrt n + 1 := by
  simpa [core, prefixCount, prefixFinset, Nat.count_eq_card_filter_range] using
    count_sparseSquare_le_sqrt_add_one n

theorem generatorFirst_subset_range (input output : Stream) :
    GenLimit.GeneratorFirst input output ⊆ Set.range output := by
  rintro x ⟨t, htx, _⟩
  exact ⟨t, htx⟩

theorem range_subset_core_union_sample {output : Stream} {T : ℕ}
    (hT : ∀ t, T ≤ t → output t ∈ core) :
    Set.range output ⊆ core ∪ (↑(GenLimit.sample output T) : Set ℕ) := by
  rintro x ⟨t, rfl⟩
  by_cases ht : T ≤ t
  · exact Or.inl (hT t ht)
  · exact Or.inr (GenLimit.mem_sample_iff.mpr ⟨t, Nat.lt_of_not_ge ht, rfl⟩)

theorem prefixCount_union_finset_le (A : Set ℕ) (S : Finset ℕ) (n : ℕ) :
    prefixCount (A ∪ (↑S : Set ℕ)) n ≤ prefixCount A n + S.card := by
  classical
  have hsub : prefixFinset (A ∪ (↑S : Set ℕ)) n ⊆ prefixFinset A n ∪ S := by
    intro x hx
    rw [mem_prefixFinset] at hx
    rcases hx.2 with hxA | hxS
    · exact Finset.mem_union_left _ (mem_prefixFinset.mpr ⟨hx.1, hxA⟩)
    · exact Finset.mem_union_right _ hxS
  exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)

theorem density_univ_zero_of_eventually_core (input output : Stream)
    (h : GenLimit.NovelGeneratesInLimit input output core) :
    relativeUpperDensity (GenLimit.GeneratorFirst input output) Set.univ = 0 := by
  obtain ⟨T, hT⟩ := h
  let S := GenLimit.sample output T
  have hsub : GenLimit.GeneratorFirst input output ⊆ core ∪ (↑S : Set ℕ) :=
    (generatorFirst_subset_range input output).trans
      (range_subset_core_union_sample (fun t ht => (hT t ht).1))
  have hbound (n : ℕ) :
      prefixCount (GenLimit.GeneratorFirst input output ∩ Set.univ) n
        ≤ Nat.sqrt n + 1 + S.card := by
    rw [Set.inter_univ]
    exact (prefixCount_mono hsub n).trans
      ((prefixCount_union_finset_le core S n).trans
        (Nat.add_le_add_right (prefixCount_core_le n) S.card))
  have hupper : Tendsto
      (fun n : ℕ => (((Nat.sqrt n : ℝ) + 1) + S.card) / (n : ℝ))
      atTop (𝓝 0) := by
    have hs := tendsto_sparseSqrt_add_one_div
    have hc : Tendsto (fun n : ℕ => (S.card : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
      simpa using tendsto_const_div_atTop_nhds_zero_nat (S.card : ℝ)
    simpa only [add_div, zero_add] using hs.add hc
  have hratio : Tendsto
      (fun n : ℕ =>
        (prefixCount (GenLimit.GeneratorFirst input output ∩ Set.univ) n : ℝ) /
          (prefixCount (Set.univ : Set ℕ) n : ℝ)) atTop (𝓝 0) := by
    apply squeeze_zero'
      (g := fun n : ℕ => (((Nat.sqrt n : ℝ) + 1) + S.card) / (n : ℝ))
    · exact Eventually.of_forall fun n => by positivity
    · filter_upwards [eventually_ge_atTop 1] with n hn
      rw [prefixCount_univ]
      apply div_le_div_of_nonneg_right
      · exact_mod_cast hbound n
      · positivity
    · exact hupper
  exact hratio.limsup_eq

theorem relativeUpperDensity_le_one (A K : Language) :
    relativeUpperDensity A K ≤ 1 := by
  unfold relativeUpperDensity
  apply limsup_le_of_le
  · exact isCoboundedUnder_le_of_le atTop (fun _ => by positivity)
  · exact Eventually.of_forall fun n => by
      by_cases hzero : prefixCount K n = 0
      · simp [hzero]
      · have hcount := prefixCount_mono (Set.inter_subset_right : A ∩ K ⊆ K) n
        have hpos : (0 : ℝ) < prefixCount K n := by exact_mod_cast Nat.pos_of_ne_zero hzero
        rw [div_le_iff₀ hpos]
        simpa only [one_mul] using (show (prefixCount (A ∩ K) n : ℝ) ≤ (prefixCount K n : ℝ) by exact_mod_cast hcount)

def freshGenerator : OnlineGenerator := fun t inputHistory outputHistory =>
  GenLimit.Support.freshFromInfinite core core_infinite
    ((Finset.univ.image inputHistory) ∪ (Finset.univ.image outputHistory))

def freshOutput (input : Stream) : Stream
  | 0 => freshGenerator 0 (fun i => input i) (fun i => Fin.elim0 i)
  | t + 1 => freshGenerator (t + 1) (fun i => input i)
      (fun i => freshOutput input i)

theorem freshOutput_follows (input : Stream) :
    Follows freshGenerator input (freshOutput input) := by
  intro t
  cases t with
  | zero =>
      simp only [freshOutput]
      congr
      funext i
      exact Fin.elim0 i
  | succ t => simp only [freshOutput]

theorem freshOutput_novel (input : Stream) :
    GenLimit.NovelGeneratesInLimit input (freshOutput input) core := by
  refine ⟨0, fun t _ => ?_⟩
  have hmem := GenLimit.Support.freshFromInfinite_mem core core_infinite
    ((Finset.univ.image (fun i : Fin (t + 1) => input i)) ∪
      (Finset.univ.image (fun i : Fin t => freshOutput input i)))
  have hnot := GenLimit.Support.freshFromInfinite_not_mem core core_infinite
    ((Finset.univ.image (fun i : Fin (t + 1) => input i)) ∪
      (Finset.univ.image (fun i : Fin t => freshOutput input i)))
  have hout : freshOutput input t = freshGenerator t
      (fun i => input i) (fun i => freshOutput input i) :=
    freshOutput_follows input t
  rw [hout]
  refine ⟨hmem, ?_, ?_⟩
  · intro hs
    obtain ⟨s, hslt, hsin⟩ := GenLimit.mem_sample_iff.mp hs
    apply hnot
    apply Finset.mem_union_left
    exact Finset.mem_image.mpr ⟨⟨s, hslt⟩, Finset.mem_univ _, hsin⟩
  · intro s hslt heq
    apply hnot
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨⟨s, hslt⟩, Finset.mem_univ _, heq⟩

def extra (j : ℕ) : Set ℕ :=
  {x | ∃ k < j, x = sparseBetweenSquares k}

def family {r : ℕ} (j : Fin r) : Language :=
  if (j : ℕ) + 1 = r then Set.univ else core ∪ extra j

theorem core_subset_family {r : ℕ} (j : Fin r) : core ⊆ family j := by
  intro x hx
  unfold family
  split <;> simp_all

theorem family_strictlyNested {r : ℕ} (hr : 2 ≤ r) :
    StrictlyNested (@family r) := by
  intro i j hij
  by_cases hjlast : (j : ℕ) + 1 = r
  · have hj : family j = Set.univ := by simp [family, hjlast]
    have hi : family i = core ∪ extra i := by simp [family]; omega
    rw [hj, hi]
    refine Set.ssubset_iff_subset_ne.mpr ⟨Set.subset_univ _, ?_⟩
    intro heq
    have hmem : sparseBetweenSquares j ∈ core ∪ extra i := by
      rw [heq]
      trivial
    rcases hmem with hcore | ⟨k, hk, heqk⟩
    · exact sparseBetweenSquares_nonsquare j hcore
    · have hki : k = j := sparseBetweenSquares_strictMono.injective heqk.symm
      omega
  · have hi : family i = core ∪ extra i := by simp [family]; omega
    have hj : family j = core ∪ extra j := by simp [family, hjlast]
    rw [hi, hj]
    refine Set.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
    · intro x hx
      rcases hx with hx | ⟨k, hk, rfl⟩
      · exact Or.inl hx
      · exact Or.inr ⟨k, hk.trans hij, rfl⟩
    · intro heq
      have hmem : sparseBetweenSquares i ∈ core ∪ extra j :=
        Or.inr ⟨i, hij, rfl⟩
      rw [← heq] at hmem
      rcases hmem with hcore | ⟨k, hk, heqk⟩
      · exact sparseBetweenSquares_nonsquare i hcore
      · have : k = i := sparseBetweenSquares_strictMono.injective heqk.symm
        omega

theorem globallyFeasible {r : ℕ} : GloballyFeasible (@family r) := by
  refine ⟨freshGenerator, fun input _ => ⟨freshOutput input,
    freshOutput_follows input, ?_⟩⟩
  intro j
  obtain ⟨T, hT⟩ := freshOutput_novel input
  exact ⟨T, fun t ht =>
    let h := hT t ht
    ⟨core_subset_family j h.1, h.2.1, h.2.2⟩⟩

theorem pairObstruction : PairObstruction core Set.univ commonInput := by
  intro Ω _ μ _ gen output _hfollows _hmeas hint0 hint1 hvalid0 _hvalid1
  have hzero : ∀ᵐ ω ∂μ,
      relativeUpperDensity (GenLimit.GeneratorFirst commonInput (output ω)) Set.univ = 0 :=
    hvalid0.mono fun ω hω => density_univ_zero_of_eventually_core commonInput (output ω) hω
  have he1 : expectedUpperDensity μ Set.univ commonInput output = 0 := by
    unfold expectedUpperDensity
    rw [integral_congr_ae hzero]
    simp
  have he0 : expectedUpperDensity μ core commonInput output ≤ 1 := by
    unfold expectedUpperDensity
    calc
      (∫ ω, relativeUpperDensity
          (GenLimit.GeneratorFirst commonInput (output ω)) core ∂μ)
          ≤ ∫ _ω, (1 : ℝ) ∂μ := by
            apply integral_mono_ae hint0 (integrable_const 1)
            exact ae_of_all _ fun ω => relativeUpperDensity_le_one _ _
      _ = 1 := by simp
  rw [he1, add_zero]
  refine ⟨he0, ?_⟩
  rintro ⟨hhalf0, hhalf1⟩
  linarith

theorem manyTargetObstruction {r : ℕ} (hr : 2 ≤ r) :
    ManyTargetObstruction (@family r) commonInput := by
  intro Ω _ μ _ gen output _hfollows _hmeas _hint hvalid
  let j : Fin r := ⟨r - 1, by omega⟩
  refine ⟨j, ?_⟩
  have hjlast : family j = Set.univ := by
    simp [family, j, show r - 1 + 1 = r by omega]
  have hfirst : family (⟨0, by omega⟩ : Fin r) = core := by
    ext x
    simp [family, extra]
    omega
  have hcorevalid : EventuallyFreshValid μ core commonInput output := by
    filter_upwards [hvalid ⟨0, by omega⟩] with ω hω
    rw [hfirst] at hω
    exact hω
  have hzero : ∀ᵐ ω ∂μ,
      relativeUpperDensity (GenLimit.GeneratorFirst commonInput (output ω)) Set.univ = 0 :=
    hcorevalid.mono fun ω hω => density_univ_zero_of_eventually_core commonInput (output ω) hω
  rw [hjlast]
  unfold expectedUpperDensity
  rw [integral_congr_ae hzero]
  simp

end

end Case024Proof

open Case024Proof Stage3Case024 GenLimit.InfiniteContamination

theorem stage3_result : Stage3Case024.MainClaim := by
  constructor
  · refine ⟨core, Set.univ, commonInput, ?_, legal_of_core_subset Set.Subset.rfl,
      legal_of_core_subset (Set.subset_univ core), pairObstruction⟩
    refine Set.ssubset_iff_subset_ne.mpr ⟨Set.subset_univ _, ?_⟩
    intro heq
    have hmem : sparseBetweenSquares 0 ∈ core := by rw [heq]; trivial
    exact sparseBetweenSquares_nonsquare 0 hmem
  · intro r hr
    refine ⟨@family r, commonInput, family_strictlyNested hr, ?_, globallyFeasible,
      manyTargetObstruction hr⟩
    intro j
    exact legal_of_core_subset (core_subset_family j)
