import Stage3Model
import GenLimit.Paper17_InfiniteContamination.SharedVanishingPresentation
import Mathlib.Tactic

open Filter MeasureTheory
open scoped Topology BigOperators

namespace Case024

open Stage3Case024
open GenLimit.InfiniteContamination

noncomputable local instance : DecidablePred SparseSquare := Classical.decPred _

abbrev Squares : Set ℕ := {n | SparseSquare n}
abbrev NonSquares : Set ℕ := Squaresᶜ

lemma squares_infinite : Squares.Infinite := by
  have hinj : Function.Injective (fun n : ℕ => n * n) := by
    intro a b hab
    exact Nat.mul_self_inj.mp hab
  exact (Set.infinite_range_of_injective hinj).mono (by
    rintro _ ⟨n, rfl⟩
    exact sparseSquare_mul_self n)

noncomputable def commonInput : Stream :=
  sparseMergePresentation Squares NonSquares squares_infinite

lemma commonInput_injective : Function.Injective commonInput := by
  apply sparseMergePresentation_injective squares_infinite
  rw [Set.disjoint_left]
  intro x hx hxcomp
  exact hxcomp hx

lemma commonInput_range : Set.range commonInput = Set.univ := by
  rw [commonInput, range_sparseMergePresentation squares_infinite]
  exact Set.union_compl_self Squares

lemma legal_commonInput {K : Language} (hSquares : Squares ⊆ K) :
    Legal commonInput K := by
  refine ⟨squares_infinite.mono hSquares, commonInput_injective, ?_, ?_⟩
  · rw [GenLimit.InfiniteContamination.NoOmissions, commonInput_range]
    exact Set.subset_univ K
  · exact sparseMergePresentation_vanishingNoise_of_core_subset
      squares_infinite hSquares

lemma prefixCount_mono {A B : Set ℕ} (hAB : A ⊆ B) (n : ℕ) :
    GenLimit.PatientScope.prefixCount A n ≤
      GenLimit.PatientScope.prefixCount B n := by
  unfold GenLimit.PatientScope.prefixCount
  apply Finset.card_le_card
  intro x hx
  rw [GenLimit.PatientScope.mem_prefixFinset] at hx ⊢
  exact ⟨hx.1, hAB hx.2⟩

lemma prefixCount_univ (n : ℕ) :
    GenLimit.PatientScope.prefixCount (Set.univ : Set ℕ) n = n := by
  simp [GenLimit.PatientScope.prefixCount, GenLimit.PatientScope.prefixFinset]

lemma prefixCount_squares (n : ℕ) :
    GenLimit.PatientScope.prefixCount Squares n = Nat.count SparseSquare n := by
  classical
  rw [Nat.count_eq_card_filter_range]
  rfl

lemma relativeUpperDensity_le_one (A K : Language) :
    relativeUpperDensity A K ≤ 1 := by
  unfold relativeUpperDensity
  apply Filter.limsup_le_of_le
    (isCoboundedUnder_le_of_le atTop (fun n =>
      div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))
  filter_upwards [] with n
  let a := GenLimit.PatientScope.prefixCount (A ∩ K) n
  let b := GenLimit.PatientScope.prefixCount K n
  have hab : a ≤ b := prefixCount_mono Set.inter_subset_right n
  by_cases hb : b = 0
  · simp [b, hb, Nat.eq_zero_of_le_zero (hab.trans (Nat.le_of_eq hb))]
  · have hbpos : (0 : ℝ) < b := by exact_mod_cast Nat.pos_of_ne_zero hb
    rw [div_le_one hbpos]
    exact_mod_cast hab

lemma prefixCount_le_squares_add_finite {A : Set ℕ}
    (hfinite : (A \ Squares).Finite) (n : ℕ) :
    GenLimit.PatientScope.prefixCount A n ≤
      GenLimit.PatientScope.prefixCount Squares n + hfinite.toFinset.card := by
  classical
  unfold GenLimit.PatientScope.prefixCount
  calc
    (GenLimit.PatientScope.prefixFinset A n).card ≤
        (GenLimit.PatientScope.prefixFinset Squares n ∪ hfinite.toFinset).card := by
      apply Finset.card_le_card
      intro x hx
      have hx' := GenLimit.PatientScope.mem_prefixFinset.mp hx
      by_cases hs : x ∈ Squares
      · exact Finset.mem_union_left _
          (GenLimit.PatientScope.mem_prefixFinset.mpr ⟨hx'.1, hs⟩)
      · exact Finset.mem_union_right _ ((Set.Finite.mem_toFinset hfinite).2 ⟨hx'.2, hs⟩)
    _ ≤ (GenLimit.PatientScope.prefixFinset Squares n).card + hfinite.toFinset.card :=
      Finset.card_union_le _ _

lemma ambientRatio_tendsto_zero {A : Set ℕ}
    (hfinite : (A \ Squares).Finite) :
    Tendsto
      (fun n : ℕ =>
        (GenLimit.PatientScope.prefixCount A n : ℝ) / (n : ℝ))
      atTop (𝓝 0) := by
  let c : ℕ := hfinite.toFinset.card
  have hbound : ∀ n : ℕ,
      (GenLimit.PatientScope.prefixCount A n : ℝ) / (n : ℝ) ≤
        ((Nat.sqrt n : ℝ) + 1 + c) / (n : ℝ) := by
    intro n
    by_cases hn : n = 0
    · simp [hn]
    · apply div_le_div_of_nonneg_right
      · exact_mod_cast (prefixCount_le_squares_add_finite hfinite n |>.trans
          (by simpa [prefixCount_squares, c] using
            Nat.add_le_add_right (count_sparseSquare_le_sqrt_add_one n) c))
      · positivity
  have hc : Tendsto (fun n : ℕ => (c : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using
      (tendsto_inverse_atTop_nhds_zero_nat.const_mul (c : ℝ))
  have htop : Tendsto
      (fun n : ℕ => ((Nat.sqrt n : ℝ) + 1 + c) / (n : ℝ))
      atTop (𝓝 0) := by
    convert tendsto_sparseSqrt_add_one_div.add hc using 1
    · funext n
      ring
    · ring
  exact squeeze_zero
    (fun n => div_nonneg (by positivity) (by positivity)) hbound htop

lemma relativeUpperDensity_univ_eq_zero {A : Language}
    (hfinite : (A \ Squares).Finite) :
    relativeUpperDensity A Set.univ = 0 := by
  unfold relativeUpperDensity
  have hfun :
      (fun n : ℕ =>
        (GenLimit.PatientScope.prefixCount (A ∩ Set.univ) n : ℝ) /
          (GenLimit.PatientScope.prefixCount Set.univ n : ℝ)) =
      (fun n : ℕ =>
        (GenLimit.PatientScope.prefixCount A n : ℝ) / (n : ℝ)) := by
    funext n
    simp [prefixCount_univ]
  rw [hfun]
  exact (ambientRatio_tendsto_zero hfinite).limsup_eq

lemma generatorFirst_diff_finite {input output : Stream} {K : Language}
    (hvalid : GenLimit.NovelGeneratesInLimit input output K) :
    (GenLimit.GeneratorFirst input output \ K).Finite := by
  obtain ⟨T, hT⟩ := hvalid
  apply (Set.finite_range (fun t : Fin T => output t)).subset
  intro x hx
  obtain ⟨⟨t, hout, -⟩, hxK⟩ := hx
  have ht : t < T := by
    by_contra hnot
    have houtK := (hT t (Nat.le_of_not_gt hnot)).1
    rw [hout] at houtK
    exact hxK houtK
  exact ⟨⟨t, ht⟩, hout⟩

noncomputable def safeGenerator : OnlineGenerator :=
  fun t input previous =>
    let base := 1 + (∑ i, input i) + (∑ i, previous i)
    base * base

noncomputable def safeOutput (input : Stream) (t : ℕ) : ℕ :=
  safeGenerator t (fun i => input i) (fun i => safeOutput input i)
termination_by t

decreasing_by omega

lemma safeOutput_follows (input : Stream) :
    Follows safeGenerator input (safeOutput input) := by
  intro t
  exact safeOutput.eq_def input t

lemma le_input_sum {t : ℕ} (input : Fin (t + 1) → ℕ) (i : Fin (t + 1)) :
    input i ≤ ∑ j, input j := by
  exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)

lemma le_previous_sum {t : ℕ} (previous : Fin t → ℕ) (i : Fin t) :
    previous i ≤ ∑ j, previous j := by
  exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)

lemma safeGenerator_square (t : ℕ) (input : Fin (t + 1) → ℕ)
    (previous : Fin t → ℕ) :
    safeGenerator t input previous ∈ Squares := by
  let base := 1 + (∑ i, input i) + (∑ i, previous i)
  exact ⟨base, by simp [safeGenerator, base]⟩

lemma safeGenerator_fresh_input (t : ℕ) (input : Fin (t + 1) → ℕ)
    (previous : Fin t → ℕ) (i : Fin (t + 1)) :
    input i ≠ safeGenerator t input previous := by
  have hle := le_input_sum input i
  let base := 1 + (∑ j, input j) + (∑ j, previous j)
  change input i ≠ base * base
  have hbase : input i < base := by
    dsimp [base]
    omega
  have hpos : 0 < base := by
    dsimp [base]
    omega
  have hsq : base ≤ base * base := by nlinarith
  exact ne_of_lt (hbase.trans_le hsq)

lemma safeGenerator_fresh_previous (t : ℕ) (input : Fin (t + 1) → ℕ)
    (previous : Fin t → ℕ) (i : Fin t) :
    previous i ≠ safeGenerator t input previous := by
  have hle := le_previous_sum previous i
  let base := 1 + (∑ j, input j) + (∑ j, previous j)
  change previous i ≠ base * base
  have hbase : previous i < base := by
    dsimp [base]
    omega
  have hpos : 0 < base := by
    dsimp [base]
    omega
  have hsq : base ≤ base * base := by nlinarith
  exact ne_of_lt (hbase.trans_le hsq)

lemma safeOutput_novel (input : Stream) :
    GenLimit.NovelGeneratesInLimit input (safeOutput input) Squares := by
  refine ⟨0, ?_⟩
  intro t _ht
  rw [safeOutput.eq_def]
  refine ⟨safeGenerator_square t (fun i => input i) (fun i => safeOutput input i), ?_, ?_⟩
  · intro hmem
    rw [GenLimit.mem_sample_iff] at hmem
    obtain ⟨i, hi, heq⟩ := hmem
    exact safeGenerator_fresh_input t (fun i => input i) (fun i => safeOutput input i)
      ⟨i, by omega⟩ heq
  · intro s hst heq
    exact safeGenerator_fresh_previous t (fun i => input i) (fun i => safeOutput input i)
      ⟨s, hst⟩ heq

lemma safeOutput_novel_of_square_subset {K : Language} (hSquares : Squares ⊆ K)
    (input : Stream) :
    EventuallyFreshValidPath K input (safeOutput input) := by
  obtain ⟨T, hT⟩ := safeOutput_novel input
  refine ⟨T, ?_⟩
  intro t ht
  obtain ⟨hmem, hfresh, hnovel⟩ := hT t ht
  exact ⟨hSquares hmem, hfresh, hnovel⟩

noncomputable def exceptions (m : ℕ) : Set ℕ :=
  ↑((Finset.range m).image sparseBetweenSquares)

lemma exceptions_mono {a b : ℕ} (hab : a ≤ b) : exceptions a ⊆ exceptions b := by
  intro x hx
  simp only [exceptions, Finset.mem_coe, Finset.mem_image, Finset.mem_range] at hx ⊢
  obtain ⟨k, hk, rfl⟩ := hx
  exact ⟨k, hk.trans_le hab, rfl⟩

lemma between_mem_exceptions {a b : ℕ} (hab : a < b) :
    sparseBetweenSquares a ∈ exceptions b := by
  simp only [exceptions, Finset.mem_coe, Finset.mem_image, Finset.mem_range]
  exact ⟨a, hab, rfl⟩

lemma between_not_mem_exceptions (a : ℕ) :
    sparseBetweenSquares a ∉ exceptions a := by
  simp only [exceptions, Finset.mem_coe, Finset.mem_image, Finset.mem_range]
  rintro ⟨k, hk, heq⟩
  have := sparseBetweenSquares_strictMono.injective heq
  omega

noncomputable def family (r : ℕ) (i : Fin r) : Language :=
  if i.val + 1 = r then Set.univ else Squares ∪ exceptions i.val

lemma squares_subset_family (r : ℕ) (i : Fin r) : Squares ⊆ family r i := by
  intro x hx
  simp only [family]
  split
  · exact Set.mem_univ x
  · exact Set.mem_union_left _ hx

lemma family_zero {r : ℕ} (hr : 2 ≤ r) : family r ⟨0, by omega⟩ = Squares := by
  ext x
  simp [family, exceptions]
  omega

lemma family_last {r : ℕ} (hr : 1 ≤ r) :
    family r ⟨r - 1, by omega⟩ = Set.univ := by
  simp [family, Nat.sub_add_cancel hr]

lemma family_strictlyNested {r : ℕ} (hr : 2 ≤ r) :
    StrictlyNested (family r) := by
  intro i j hij
  have hiNotLast : i.val + 1 ≠ r := by omega
  by_cases hjLast : j.val + 1 = r
  · simp [family, hjLast, hiNotLast]
    apply Set.ssubset_iff_subset_ne.mpr
    refine ⟨Set.subset_univ _, ?_⟩
    intro heq
    let witness := sparseBetweenSquares r
    have hwUniv : witness ∈ (Set.univ : Set ℕ) := Set.mem_univ _
    have hwNotSquare : witness ∉ Squares := sparseBetweenSquares_nonsquare r
    have hwNotException : witness ∉ exceptions i.val := by
      simp only [exceptions, Finset.mem_coe, Finset.mem_image, Finset.mem_range]
      rintro ⟨k, hk, heqk⟩
      have hkr := sparseBetweenSquares_strictMono.injective heqk
      omega
    rw [← heq] at hwUniv
    rcases hwUniv with hwSquare | hwException
    · exact hwNotSquare hwSquare
    · exact hwNotException hwException
  · simp [family, hjLast, hiNotLast]
    apply Set.ssubset_iff_subset_ne.mpr
    refine ⟨Set.union_subset_union_right _ (exceptions_mono (Nat.le_of_lt hij)), ?_⟩
    intro heq
    have hw : sparseBetweenSquares i.val ∈ Squares ∪ exceptions j.val :=
      Set.mem_union_right _ (between_mem_exceptions hij)
    rw [← heq] at hw
    rcases hw with hwSquare | hwException
    · exact sparseBetweenSquares_nonsquare i.val hwSquare
    · exact between_not_mem_exceptions i.val hwException

lemma family_legal (r : ℕ) (i : Fin r) : Legal commonInput (family r i) :=
  legal_commonInput (squares_subset_family r i)

lemma family_globallyFeasible (r : ℕ) : GloballyFeasible (family r) := by
  refine ⟨safeGenerator, ?_⟩
  intro input _hlegal
  exact ⟨safeOutput input, safeOutput_follows input,
    fun j => safeOutput_novel_of_square_subset (squares_subset_family r j) input⟩

end Case024
