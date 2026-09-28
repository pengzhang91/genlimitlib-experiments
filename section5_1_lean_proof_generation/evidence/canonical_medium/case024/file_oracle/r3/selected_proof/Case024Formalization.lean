import Case024Helpers

open Filter MeasureTheory
open scoped Topology

namespace Stage3Case024Proof

open GenLimit
open GenLimit.InfiniteContamination
open Stage3Case024

noncomputable def commonStream : Stream :=
  sparseMergePresentation Squares (Set.univ \ Squares) squares_infinite

theorem commonStream_injective : Function.Injective commonStream := by
  apply sparseMergePresentation_injective squares_infinite
  exact Set.disjoint_sdiff_right

theorem commonStream_range : Set.range commonStream = Set.univ := by
  rw [commonStream, range_sparseMergePresentation squares_infinite]
  exact Set.union_diff_cancel (Set.subset_univ Squares)

theorem legal_commonStream {K : Stage3Case024.Language} (hcore : Squares ⊆ K) :
    Legal commonStream K := by
  constructor
  · exact squares_infinite.mono hcore
  · refine ⟨commonStream_injective, ?_, ?_⟩
    · rw [GenLimit.InfiniteContamination.NoOmissions, commonStream_range]
      exact Set.subset_univ _
    · exact sparseMergePresentation_vanishingNoise_of_core_subset
        squares_infinite hcore

theorem pair_obstruction : PairObstruction Squares Set.univ commonStream := by
  intro Ω _ μ _ gen output _ _ hInt0 hInt1 hValid0 _
  have hzero : (fun ω => relativeUpperDensity
      (GeneratorFirst commonStream (output ω)) Set.univ) =ᵐ[μ] 0 := by
    filter_upwards [hValid0] with ω hω
    exact relativeUpperDensity_univ_eq_zero hω
  have hE1 : expectedUpperDensity μ Set.univ commonStream output = 0 := by
    exact integral_eq_zero_of_ae hzero
  have hE0 : expectedUpperDensity μ Squares commonStream output ≤ 1 := by
    calc
      expectedUpperDensity μ Squares commonStream output ≤ ∫ _ : Ω, (1 : ℝ) ∂μ := by
        apply integral_mono_ae hInt0 (integrable_const 1)
        exact Eventually.of_forall fun ω => relativeUpperDensity_le_one _ _
      _ = 1 := by simp
  constructor
  · rw [hE1, add_zero]
    exact hE0
  · rintro ⟨hhalf0, hhalf1⟩
    rw [hE1] at hhalf1
    norm_num at hhalf1


def nonsquarePoint (k : ℕ) : ℕ := sparseBetweenSquares k

theorem nonsquarePoint_injective : Function.Injective nonsquarePoint :=
  sparseBetweenSquares_strictMono.injective

theorem nonsquarePoint_not_square (k : ℕ) : nonsquarePoint k ∉ Squares :=
  sparseBetweenSquares_nonsquare k

noncomputable def extras (i : ℕ) : Set ℕ :=
  ↑((Finset.range i).image nonsquarePoint)

noncomputable def nestedFamily (r : ℕ) (j : Fin r) : Stage3Case024.Language :=
  if j.val = r - 1 then Set.univ else Squares ∪ extras j.val

theorem nestedFamily_core (r : ℕ) (j : Fin r) :
    Squares ⊆ nestedFamily r j := by
  intro x hx
  unfold nestedFamily
  split <;> simp_all

theorem nestedFamily_zero {r : ℕ} (hr : 2 ≤ r) :
    nestedFamily r ⟨0, by omega⟩ = Squares := by
  have hzero : (0 : ℕ) ≠ r - 1 := by omega
  simp [nestedFamily, hzero, extras]

theorem nestedFamily_last {r : ℕ} (hr : 2 ≤ r) :
    nestedFamily r ⟨r - 1, by omega⟩ = Set.univ := by
  simp [nestedFamily]

theorem nestedFamily_strict {r : ℕ} (hr : 2 ≤ r) :
    StrictlyNested (nestedFamily r) := by
  intro i j hij
  rw [Set.ssubset_iff_subset_ne]
  have hiLast : i.val ≠ r - 1 := by omega
  by_cases hjLast : j.val = r - 1
  · constructor
    · simp [nestedFamily, hiLast, hjLast]
    · intro heq
      have hmem : nonsquarePoint i.val ∈ nestedFamily r i := by
        rw [heq]
        simp [nestedFamily, hjLast]
      have hs : nonsquarePoint i.val ∈ Squares := by
        rcases (by simpa [nestedFamily, hiLast] using hmem :
          nonsquarePoint i.val ∈ Squares ∪ extras i.val) with hs | he
        · exact hs
        · simp [extras] at he
          obtain ⟨k, hk, hki⟩ := he
          have := nonsquarePoint_injective hki
          omega
      exact nonsquarePoint_not_square i.val hs
  · constructor
    · intro x hx
      have hx' : x ∈ Squares ∪ extras i.val := by
        simpa [nestedFamily, hiLast] using hx
      have : x ∈ Squares ∪ extras j.val := by
        rcases hx' with hxS | hxE
        · exact Or.inl hxS
        · right
          simp [extras] at hxE ⊢
          obtain ⟨k, hk, hkx⟩ := hxE
          exact ⟨k, lt_trans hk hij, hkx⟩
      simpa [nestedFamily, hjLast] using this
    · intro heq
      have hmemJ : nonsquarePoint i.val ∈ nestedFamily r j := by
        have : nonsquarePoint i.val ∈ Squares ∪ extras j.val := by
          right
          simp [extras]
          exact ⟨i.val, hij, rfl⟩
        simpa [nestedFamily, hjLast] using this
      have hmemI : nonsquarePoint i.val ∈ nestedFamily r i := heq ▸ hmemJ
      have hi : nonsquarePoint i.val ∈ Squares ∪ extras i.val := by
        simpa [nestedFamily, hiLast] using hmemI
      rcases hi with hs | he
      · exact nonsquarePoint_not_square i.val hs
      · simp [extras] at he
        obtain ⟨k, hk, hki⟩ := he
        have := nonsquarePoint_injective hki
        omega

theorem nestedFamily_legal {r : ℕ} (hr : 2 ≤ r) :
    ∀ j, Legal commonStream (nestedFamily r j) := by
  intro j
  exact legal_commonStream (nestedFamily_core r j)

theorem novel_mono {input output : Stream} {A B : Set ℕ}
    (hAB : A ⊆ B) (h : NovelGeneratesInLimit input output A) :
    NovelGeneratesInLimit input output B := by
  obtain ⟨T, hT⟩ := h
  exact ⟨T, fun t ht => ⟨hAB (hT t ht).1, (hT t ht).2⟩⟩

theorem nestedFamily_feasible {r : ℕ} (hr : 2 ≤ r) :
    GloballyFeasible (nestedFamily r) := by
  refine ⟨squareGenerator, ?_⟩
  intro input _
  refine ⟨runGenerator squareGenerator input,
    runGenerator_follows squareGenerator input, ?_⟩
  intro j
  apply novel_mono (nestedFamily_core r j)
  exact squareGenerator_novel input _
    (runGenerator_follows squareGenerator input)

theorem nestedFamily_obstruction {r : ℕ} (hr : 2 ≤ r) :
    ManyTargetObstruction (nestedFamily r) commonStream := by
  intro Ω _ μ _ gen output _ _ _ hValid
  let j0 : Fin r := ⟨0, by omega⟩
  let jlast : Fin r := ⟨r - 1, by omega⟩
  have hSq : EventuallyFreshValid μ Squares commonStream output := by
    simpa [j0, nestedFamily_zero hr] using hValid j0
  refine ⟨jlast, ?_⟩
  rw [show nestedFamily r jlast = Set.univ by
    simpa [jlast] using nestedFamily_last hr]
  apply integral_eq_zero_of_ae
  filter_upwards [hSq] with ω hω
  exact relativeUpperDensity_univ_eq_zero hω

theorem many_target_witness {r : ℕ} (hr : 2 ≤ r) :
    ManyTargetWitness (nestedFamily r) commonStream := by
  exact ⟨nestedFamily_strict hr, nestedFamily_legal hr,
    nestedFamily_feasible hr, nestedFamily_obstruction hr⟩

end Stage3Case024Proof

open Stage3Case024Proof

theorem stage3_result : Stage3Case024.MainClaim := by
  constructor
  · refine ⟨Squares, Set.univ, commonStream, ?_,
      legal_commonStream Set.Subset.rfl, legal_commonStream (Set.subset_univ Squares),
      pair_obstruction⟩
    rw [Set.ssubset_iff_subset_ne]
    refine ⟨Set.subset_univ _, ?_⟩
    intro h
    have : nonsquarePoint 0 ∈ Squares := by rw [h]; simp
    exact nonsquarePoint_not_square 0 this
  · intro r hr
    exact ⟨nestedFamily r, commonStream, many_target_witness hr⟩
