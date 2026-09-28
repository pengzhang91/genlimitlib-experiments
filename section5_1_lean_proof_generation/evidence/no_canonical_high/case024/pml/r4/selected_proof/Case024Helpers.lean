import Stage3Model
import GenLimit.Paper17_InfiniteContamination.SharedVanishingPresentation

open Filter MeasureTheory
open scoped Topology

namespace Stage3Case024

namespace Case024

def core : Language := {n | GenLimit.InfiniteContamination.SparseSquare n}

def extra (k : ℕ) : ℕ :=
  GenLimit.InfiniteContamination.sparseBetweenSquares k

theorem extra_injective : Function.Injective extra :=
  GenLimit.InfiniteContamination.sparseBetweenSquares_strictMono.injective

theorem extra_not_core (k : ℕ) : extra k ∉ core :=
  GenLimit.InfiniteContamination.sparseBetweenSquares_nonsquare k

theorem core_infinite : core.Infinite := by
  have hinj : Function.Injective (fun k : ℕ => k * k) := by
    intro a b hab
    nlinarith
  apply (Set.infinite_range_of_injective hinj).mono
  rintro _ ⟨k, rfl⟩
  exact GenLimit.InfiniteContamination.sparseSquare_mul_self k

def finiteExtras (i : ℕ) : Language :=
  {x | ∃ k < i, extra k = x}

def family {r : ℕ} (i : Fin r) : Language :=
  if i.1 + 1 = r then Set.univ else core ∪ finiteExtras i.1

noncomputable def input : Stream :=
  GenLimit.InfiniteContamination.sparseMergePresentation
    core coreᶜ core_infinite

theorem input_injective : Function.Injective input := by
  apply GenLimit.InfiniteContamination.sparseMergePresentation_injective
  rw [Set.disjoint_left]
  intro x hx hxc
  exact hxc hx

theorem input_range : Set.range input = Set.univ := by
  rw [input, GenLimit.InfiniteContamination.range_sparseMergePresentation]
  exact Set.union_compl_self core

theorem core_subset_family {r : ℕ} (i : Fin r) : core ⊆ family i := by
  intro x hx
  simp only [family]
  split
  · simp
  · exact Set.mem_union_left _ hx

theorem family_infinite {r : ℕ} (i : Fin r) : (family i).Infinite :=
  core_infinite.mono (core_subset_family i)

theorem input_legal_family {r : ℕ} (i : Fin r) : Legal input (family i) := by
  refine ⟨family_infinite i, input_injective, ?_, ?_⟩
  · intro x hx
    rw [input_range]
    trivial
  · exact
      GenLimit.InfiniteContamination.sparseMergePresentation_vanishingNoise_of_core_subset
        core_infinite (core_subset_family i)

theorem finiteExtras_mono {i j : ℕ} (hij : i ≤ j) :
    finiteExtras i ⊆ finiteExtras j := by
  rintro x ⟨k, hk, rfl⟩
  exact ⟨k, lt_of_lt_of_le hk hij, rfl⟩

theorem extra_mem_finiteExtras {i k : ℕ} (hk : k < i) :
    extra k ∈ finiteExtras i :=
  ⟨k, hk, rfl⟩

theorem extra_not_mem_finiteExtras (i : ℕ) : extra i ∉ finiteExtras i := by
  rintro ⟨k, hk, hki⟩
  have : k = i := extra_injective hki
  omega

def firstIndex {r : ℕ} (hr : 0 < r) : Fin r := ⟨0, hr⟩

def topIndex {r : ℕ} (hr : 0 < r) : Fin r := ⟨r - 1, by omega⟩

theorem family_first_eq_core {r : ℕ} (hr : 2 ≤ r) :
    family (firstIndex (by omega : 0 < r)) = core := by
  ext x
  simp [family, firstIndex, finiteExtras]
  omega

theorem family_top_eq_univ {r : ℕ} (hr : 0 < r) :
    family (topIndex hr) = Set.univ := by
  simp [family, topIndex]
  omega

theorem core_ssubset_univ : core ⊂ (Set.univ : Language) := by
  refine Set.ssubset_iff_subset_ne.mpr ⟨Set.subset_univ _, ?_⟩
  intro heq
  have hmem : extra 0 ∈ core := by rw [heq]; trivial
  exact extra_not_core 0 hmem

theorem family_strictlyNested {r : ℕ} : StrictlyNested (@family r) := by
  intro i j hij
  have hiNotLast : i.1 + 1 ≠ r := by omega
  rw [family, if_neg hiNotLast]
  by_cases hjLast : j.1 + 1 = r
  · rw [family, if_pos hjLast]
    refine Set.ssubset_iff_subset_ne.mpr ⟨Set.subset_univ _, ?_⟩
    intro heq
    have hall : extra i.1 ∈ core ∪ finiteExtras i.1 := by
      rw [heq]
      trivial
    rcases hall with hcore | hfinite
    · exact extra_not_core i.1 hcore
    · exact extra_not_mem_finiteExtras i.1 hfinite
  · rw [family, if_neg hjLast]
    refine Set.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
    · intro x hx
      rcases hx with hx | hx
      · exact Set.mem_union_left _ hx
      · exact Set.mem_union_right _ (finiteExtras_mono (Nat.le_of_lt hij) hx)
    · intro heq
      have hmem : extra i.1 ∈ core ∪ finiteExtras j.1 :=
        Set.mem_union_right _ (extra_mem_finiteExtras hij)
      rw [← heq] at hmem
      rcases hmem with hcore | hfinite
      · exact extra_not_core i.1 hcore
      · exact extra_not_mem_finiteExtras i.1 hfinite

noncomputable def historyMax {t : ℕ} (xs : Fin (t + 1) → ℕ) : ℕ :=
  Finset.univ.sup xs

theorem history_le_max {t : ℕ} (xs : Fin (t + 1) → ℕ) (i : Fin (t + 1)) :
    xs i ≤ historyMax xs := by
  exact Finset.le_sup (Finset.mem_univ i)

def squareAbove (t m : ℕ) : ℕ :=
  (t + m + 1) * (t + m + 1)

noncomputable def feasibleGenerator : OnlineGenerator :=
  fun t xs _ => squareAbove t (historyMax xs)

noncomputable def feasibleOutput (stream : Stream) : Stream :=
  fun t => squareAbove t (historyMax (fun i : Fin (t + 1) => stream i))

theorem feasible_follows (stream : Stream) :
    Follows feasibleGenerator stream (feasibleOutput stream) := by
  intro t
  rfl

theorem squareAbove_mem_core (t m : ℕ) : squareAbove t m ∈ core := by
  exact ⟨t + m + 1, rfl⟩

theorem feasibleOutput_fresh (stream : Stream) (t : ℕ) :
    feasibleOutput stream t ∉ GenLimit.sample stream (t + 1) := by
  rw [GenLimit.mem_sample_iff]
  rintro ⟨s, hs, heq⟩
  let xs : Fin (t + 1) → ℕ := fun i => stream i
  have hle : stream s ≤ historyMax xs :=
    history_le_max xs ⟨s, hs⟩
  have hlt : historyMax xs < feasibleOutput stream t := by
    simp only [feasibleOutput, squareAbove, xs]
    nlinarith
  omega

theorem feasibleOutput_injective (stream : Stream) :
    Function.Injective (feasibleOutput stream) := by
  intro s t heq
  by_cases hst : s < t
  · let xs : Fin (s + 1) → ℕ := fun i => stream i
    let xt : Fin (t + 1) → ℕ := fun i => stream i
    have hmax : historyMax xs ≤ historyMax xt := by
      apply Finset.sup_le
      intro i hi
      exact history_le_max xt
        ⟨i.1, lt_of_lt_of_le i.2 (Nat.succ_le_succ (Nat.le_of_lt hst))⟩
    simp only [feasibleOutput, squareAbove] at heq
    have hbase : s + historyMax xs + 1 < t + historyMax xt + 1 := by omega
    nlinarith
  · by_cases hts : t < s
    · let xs : Fin (s + 1) → ℕ := fun i => stream i
      let xt : Fin (t + 1) → ℕ := fun i => stream i
      have hmax : historyMax xt ≤ historyMax xs := by
        apply Finset.sup_le
        intro i hi
        exact history_le_max xs
          ⟨i.1, lt_of_lt_of_le i.2 (Nat.succ_le_succ (Nat.le_of_lt hts))⟩
      simp only [feasibleOutput, squareAbove] at heq
      have hbase : t + historyMax xt + 1 < s + historyMax xs + 1 := by omega
      nlinarith
    · omega

theorem feasible_eventually (stream : Stream) {r : ℕ} (j : Fin r) :
    EventuallyFreshValidPath (family j) stream (feasibleOutput stream) := by
  refine ⟨0, ?_⟩
  intro t _
  refine ⟨core_subset_family j (squareAbove_mem_core _ _),
    feasibleOutput_fresh stream t, ?_⟩
  intro s hs hEq
  have hst := (feasibleOutput_injective stream) hEq
  omega

theorem family_globallyFeasible {r : ℕ} : GloballyFeasible (@family r) := by
  refine ⟨feasibleGenerator, ?_⟩
  intro stream _
  exact ⟨feasibleOutput stream, feasible_follows stream,
    fun j => feasible_eventually stream j⟩

theorem generatorFirst_subset_range (stream output : Stream) :
    GenLimit.GeneratorFirst stream output ⊆ Set.range output := by
  rintro x ⟨t, htx, -⟩
  exact ⟨t, htx⟩

theorem range_diff_core_finite {output : Stream}
    (h : GenLimit.NovelGeneratesInLimit input output core) :
    (Set.range output \ core).Finite := by
  obtain ⟨T, hT⟩ := h
  apply (Set.finite_range fun t : Fin T => output t).subset
  rintro x ⟨⟨t, rfl⟩, htcore⟩
  have ht : t < T := by
    by_contra hn
    exact htcore (hT t (Nat.le_of_not_gt hn)).1
  exact ⟨⟨t, ht⟩, rfl⟩

theorem relativeUpperDensity_le_one (A K : Language) :
    relativeUpperDensity A K ≤ 1 := by
  unfold relativeUpperDensity
  apply limsup_le_of_le
  · exact isCoboundedUnder_le_of_le atTop (fun n => by positivity)
  · apply Eventually.of_forall
    intro n
    by_cases hzero : GenLimit.PatientScope.prefixCount K n = 0
    · simp [hzero]
    · exact (div_le_one (by positivity)).2 (by
        exact_mod_cast Finset.card_le_card (by
          intro x hx
          exact GenLimit.PatientScope.mem_prefixFinset.mpr
            ⟨(GenLimit.PatientScope.mem_prefixFinset.mp hx).1,
             (GenLimit.PatientScope.mem_prefixFinset.mp hx).2.2⟩))

theorem relativeUpperDensity_eq_zero_of_range_diff_core_finite
    {A : Language} (hfinite : (A \ core).Finite) :
    relativeUpperDensity A Set.univ = 0 := by
  classical
  let B := hfinite.toFinset.card
  have hbound : ∀ n,
      (GenLimit.PatientScope.prefixCount (A ∩ Set.univ) n : ℝ) /
          (GenLimit.PatientScope.prefixCount (Set.univ : Language) n : ℝ) ≤
        ((Nat.sqrt n : ℝ) + 1 + B) / n := by
    intro n
    simp only [Set.inter_univ]
    by_cases hn : n = 0
    · simp [hn, GenLimit.PatientScope.prefixCount,
        GenLimit.PatientScope.prefixFinset]
    · have hcard : GenLimit.PatientScope.prefixCount A n ≤
          Nat.count GenLimit.InfiniteContamination.SparseSquare n + B := by
        classical
        unfold GenLimit.PatientScope.prefixCount
        rw [Nat.count_eq_card_filter_range]
        let squares := (Finset.range n).filter
          GenLimit.InfiniteContamination.SparseSquare
        let exceptions := hfinite.toFinset
        have hsub : GenLimit.PatientScope.prefixFinset A n ⊆ squares ∪ exceptions := by
          intro x hx
          have hx' := GenLimit.PatientScope.mem_prefixFinset.mp hx
          by_cases hsquare : GenLimit.InfiniteContamination.SparseSquare x
          · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨
              Finset.mem_range.mpr hx'.1, hsquare⟩)
          · exact Finset.mem_union_right _ ((Set.Finite.mem_toFinset hfinite).2 ⟨hx'.2, hsquare⟩)
        calc
          (GenLimit.PatientScope.prefixFinset A n).card ≤
              (squares ∪ exceptions).card := Finset.card_le_card hsub
          _ ≤ squares.card + exceptions.card := Finset.card_union_le _ _
      have hcount : Nat.count GenLimit.InfiniteContamination.SparseSquare n + B ≤
          Nat.sqrt n + 1 + B :=
        Nat.add_le_add_right
          (GenLimit.InfiniteContamination.count_sparseSquare_le_sqrt_add_one n) B
      have hden : GenLimit.PatientScope.prefixCount (Set.univ : Language) n = n := by
        simp [GenLimit.PatientScope.prefixCount,
          GenLimit.PatientScope.prefixFinset]
      rw [hden]
      apply div_le_div_of_nonneg_right
      · exact_mod_cast hcard.trans hcount
      · positivity
  have htendsto : Tendsto
      (fun n : ℕ =>
        (GenLimit.PatientScope.prefixCount (A ∩ Set.univ) n : ℝ) /
          (GenLimit.PatientScope.prefixCount (Set.univ : Language) n : ℝ))
      atTop (𝓝 0) := by
    apply squeeze_zero
    · intro n
      positivity
    · exact hbound
    · have h1 := GenLimit.InfiniteContamination.tendsto_sparseSqrt_add_one_div
      have hB : Tendsto (fun n : ℕ => (B : ℝ) / n) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
      simpa [add_div] using h1.add hB
  exact htendsto.limsup_eq

theorem relativeUpperDensity_generatorFirst_eq_zero {output : Stream}
    (h : GenLimit.NovelGeneratesInLimit input output core) :
    relativeUpperDensity (GenLimit.GeneratorFirst input output) Set.univ = 0 := by
  apply relativeUpperDensity_eq_zero_of_range_diff_core_finite
  exact (range_diff_core_finite h).subset (Set.diff_subset_diff_left
    (generatorFirst_subset_range input output))

end Case024

end Stage3Case024
