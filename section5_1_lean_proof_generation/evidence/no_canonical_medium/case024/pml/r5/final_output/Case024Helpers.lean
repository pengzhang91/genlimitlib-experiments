import Stage3Model
import GenLimit.Paper17_InfiniteContamination.SharedVanishingPresentation
import GenLimit.Paper17_InfiniteContamination.EvenDensity
import Mathlib.Tactic

open Filter MeasureTheory
open scoped Topology

namespace Stage3Case024Proof

open Stage3Case024
open GenLimit
open GenLimit.InfiniteContamination

def squareCore : Stage3Case024.Language := {n | SparseSquare n}

def marker (k : ℕ) : ℕ :=
  let m := k + 1
  m * m + m + 1

def markerSet (k : ℕ) : Stage3Case024.Language := {n | ∃ q < k, marker q = n}

def familyLanguage (i : ℕ) : Stage3Case024.Language :=
  if i = 0 then squareCore
  else squareCore ∪ evenNaturals ∪ markerSet (i - 1)

theorem squareCore_infinite : squareCore.Infinite := by
  apply Set.infinite_of_injective_forall_mem (f := fun k => k * k)
  · intro a b hab
    nlinarith
  · intro k
    exact ⟨k, rfl⟩

theorem marker_odd (k : ℕ) : Odd (marker k) := by
  rw [odd_iff_exists_bit1]
  let m := k + 1
  rcases Nat.even_or_odd m with hm | hm
  · obtain ⟨a, ha⟩ := even_iff_exists_two_mul.mp hm
    refine ⟨a * m + a, ?_⟩
    change m * m + m + 1 = 2 * (a * m + a) + 1
    rw [ha]
    ring
  · obtain ⟨a, ha⟩ := odd_iff_exists_bit1.mp hm
    refine ⟨m * (a + 1), ?_⟩
    change m * m + m + 1 = 2 * (m * (a + 1)) + 1
    rw [ha]
    ring

theorem marker_not_square (k : ℕ) : ¬ SparseSquare (marker k) := by
  unfold SparseSquare
  apply Nat.not_exists_sq (m := k + 1)
  · simp only [marker]
    nlinarith
  · simp only [marker]
    nlinarith

theorem marker_injective : Function.Injective marker := by
  intro a b hab
  unfold marker at hab
  nlinarith

theorem squareCore_subset_familyLanguage (i : ℕ) :
    squareCore ⊆ familyLanguage i := by
  intro n hn
  by_cases hi : i = 0
  · simp [familyLanguage, hi, hn]
  · simp [familyLanguage, hi, hn]

theorem even_subset_familyLanguage_of_pos {i : ℕ} (hi : 0 < i) :
    evenNaturals ⊆ familyLanguage i := by
  intro n hn
  simp [familyLanguage, Nat.ne_of_gt hi, hn]

theorem familyLanguage_mono {i j : ℕ} (hij : i ≤ j) :
    familyLanguage i ⊆ familyLanguage j := by
  intro n hn
  by_cases hi : i = 0
  · subst i
    have hncore : n ∈ squareCore := by simpa [familyLanguage] using hn
    exact squareCore_subset_familyLanguage j hncore
  have hj : j ≠ 0 := by omega
  simp only [familyLanguage, hi, hj, if_false, Set.mem_union,
    markerSet, Set.mem_setOf_eq] at hn ⊢
  rcases hn with (hn | hn) | ⟨q, hq, rfl⟩
  · exact Or.inl (Or.inl hn)
  · exact Or.inl (Or.inr hn)
  · exact Or.inr ⟨q, by omega, rfl⟩

theorem familyLanguage_strict {i j : ℕ} (hij : i < j) :
    familyLanguage i ⊂ familyLanguage j := by
  refine Set.ssubset_iff_subset_ne.mpr ⟨familyLanguage_mono hij.le, ?_⟩
  intro heq
  by_cases hi : i = 0
  · have htwo : 2 ∈ familyLanguage j :=
      even_subset_familyLanguage_of_pos (by omega)
        (by exact even_iff_two_dvd.mpr ⟨1, by omega⟩)
    have hnotSquare : ¬ SparseSquare 2 := by
      exact Nat.not_exists_sq (m := 1) (by omega) (by omega)
    have hnot : 2 ∉ familyLanguage i := by
      simpa [familyLanguage, hi, squareCore] using hnotSquare
    exact hnot (heq ▸ htwo)
  · let q := i - 1
    have hqmem : marker q ∈ familyLanguage j := by
      have hj : j ≠ 0 := by omega
      simp only [familyLanguage, hj, if_false, Set.mem_union, markerSet,
        Set.mem_setOf_eq]
      exact Or.inr ⟨q, by omega, rfl⟩
    have hqnot : marker q ∉ familyLanguage i := by
      simp only [familyLanguage, hi, if_false, Set.mem_union, markerSet,
        Set.mem_setOf_eq]
      intro h
      rcases h with (hsq | heven) | ⟨a, ha, hae⟩
      · exact marker_not_square q hsq
      · obtain ⟨a, ha⟩ := marker_odd q
        obtain ⟨b, hb⟩ := heven
        omega
      · have : a = q := marker_injective hae
        omega
    exact hqnot (heq ▸ hqmem)

theorem familyLanguage_infinite (i : ℕ) : (familyLanguage i).Infinite :=
  squareCore_infinite.mono (squareCore_subset_familyLanguage i)

noncomputable def commonInput (r : ℕ) (_hr : 0 < r) : Stage3Case024.Stream :=
  sparseMergePresentation squareCore
    (familyLanguage (r - 1) \ squareCore) squareCore_infinite

theorem commonInput_legal (r : ℕ) (hr : 0 < r) (i : Fin r) :
    Legal (commonInput r hr) (familyLanguage i) := by
  let last : ℕ := r - 1
  have hilast : (i : ℕ) ≤ last := by
    dsimp [last]
    omega
  have hsubLast : familyLanguage i ⊆ familyLanguage last :=
    familyLanguage_mono hilast
  have hcoreSub : squareCore ⊆ familyLanguage i :=
    squareCore_subset_familyLanguage i
  have hdisjoint : Disjoint squareCore (familyLanguage last \ squareCore) :=
    Set.disjoint_sdiff_right
  have hinj : Function.Injective (commonInput r hr) := by
    exact sparseMergePresentation_injective squareCore_infinite hdisjoint
  have hrange : Set.range (commonInput r hr) = familyLanguage last := by
    rw [commonInput, range_sparseMergePresentation squareCore_infinite]
    exact Set.union_diff_cancel (squareCore_subset_familyLanguage last)
  refine ⟨familyLanguage_infinite i, hinj, ?_, ?_⟩
  · rw [GenLimit.InfiniteContamination.NoOmissions, hrange]
    exact hsubLast
  · exact sparseMergePresentation_vanishingNoise_of_core_subset
      squareCore_infinite hcoreSub

end Stage3Case024Proof

namespace Stage3Case024Proof

open Stage3Case024
open GenLimit
open GenLimit.InfiniteContamination

noncomputable local instance : DecidablePred SparseSquare := Classical.decPred _

noncomputable abbrev pcount := GenLimit.PatientScope.prefixCount

@[simp] theorem pcount_eq_naturalOrder (S : Set ℕ) (n : ℕ) :
    pcount S n = naturalOrder.prefixCount S n := rfl

@[simp] theorem pcount_squareCore (n : ℕ) :
    pcount squareCore n = Nat.count SparseSquare n := by
  classical
  rw [Nat.count_eq_card_filter_range]
  rfl

 theorem pcount_mono {A B : Set ℕ} (hAB : A ⊆ B) (n : ℕ) :
    pcount A n ≤ pcount B n := by
  unfold pcount GenLimit.PatientScope.prefixCount
  apply Finset.card_le_card
  intro x hx
  rw [GenLimit.PatientScope.mem_prefixFinset] at hx ⊢
  exact ⟨hx.1, hAB hx.2⟩

 theorem pcount_union_le (A B : Set ℕ) (n : ℕ) :
    pcount (A ∪ B) n ≤ pcount A n + pcount B n := by
  unfold pcount GenLimit.PatientScope.prefixCount
  classical
  calc
    (GenLimit.PatientScope.prefixFinset (A ∪ B) n).card ≤
        (GenLimit.PatientScope.prefixFinset A n ∪
          GenLimit.PatientScope.prefixFinset B n).card := by
      apply Finset.card_le_card
      intro x hx
      rw [GenLimit.PatientScope.mem_prefixFinset] at hx
      simp only [Finset.mem_union, GenLimit.PatientScope.mem_prefixFinset]
      rcases hx.2 with hxA | hxB
      · exact Or.inl ⟨hx.1, hxA⟩
      · exact Or.inr ⟨hx.1, hxB⟩
    _ ≤ _ := Finset.card_union_le _ _

 theorem pcount_le_ncard_of_finite {A : Set ℕ} (hA : A.Finite) (n : ℕ) :
    pcount A n ≤ A.ncard := by
  rw [Set.ncard_eq_toFinset_card A (hs := hA)]
  unfold pcount GenLimit.PatientScope.prefixCount
  apply Finset.card_le_card
  intro x hx
  rw [GenLimit.PatientScope.mem_prefixFinset] at hx
  simpa using hx.2

 theorem ratio_nonneg (A K : Set ℕ) (n : ℕ) :
    0 ≤ (pcount (A ∩ K) n : ℝ) / (pcount K n : ℝ) := by positivity

 theorem ratio_le_one (A K : Set ℕ) (n : ℕ) :
    (pcount (A ∩ K) n : ℝ) / (pcount K n : ℝ) ≤ 1 := by
  by_cases hzero : pcount K n = 0
  · have hle := pcount_mono (Set.inter_subset_right : A ∩ K ⊆ K) n
    have hnum : pcount (A ∩ K) n = 0 := by omega
    rw [hzero, hnum]
    norm_num
  · apply (div_le_one (by positivity)).2
    exact_mod_cast pcount_mono (Set.inter_subset_right) n

 theorem relativeUpperDensity_le_one (A K : Set ℕ) :
    relativeUpperDensity A K ≤ 1 := by
  unfold relativeUpperDensity
  apply limsup_le_of_le
  · exact isCoboundedUnder_le_of_le atTop (ratio_nonneg A K)
  · exact Filter.Eventually.of_forall (ratio_le_one A K)

 theorem generatorFirst_diff_finite_of_eventual
    {input output : Stage3Case024.Stream} {K : Stage3Case024.Language}
    (h : GenLimit.NovelGeneratesInLimit input output K) :
    (GenLimit.GeneratorFirst input output \ K).Finite := by
  obtain ⟨T, hT⟩ := h
  apply (Set.finite_range (fun t : Fin T => output t)).subset
  intro x hx
  obtain ⟨⟨t, htx, -⟩, hxK⟩ := hx
  have ht : t < T := by
    by_contra hnot
    apply hxK
    rw [← htx]
    exact (hT t (Nat.le_of_not_gt hnot)).1
  exact ⟨⟨t, ht⟩, htx⟩

 theorem familyLanguage_one :
    familyLanguage 1 = squareCore ∪ evenNaturals := by
  ext n
  simp [familyLanguage, markerSet]

 theorem pcount_even_lower (n : ℕ) :
    (n : ℝ) / 2 ≤ (pcount evenNaturals n : ℝ) := by
  rw [pcount_eq_naturalOrder, naturalOrder_prefixCount_even]
  have h : (n : ℝ) ≤ 2 * (((n + 1) / 2 : ℕ) : ℝ) := by
    exact_mod_cast (show n ≤ 2 * ((n + 1) / 2) by omega)
  linarith

 theorem finite_core_ratio_tendsto_zero
    (E : Set ℕ) (hE : E.Finite) :
    Tendsto
      (fun n : ℕ =>
        (pcount ((squareCore ∪ E) ∩ familyLanguage 1) n : ℝ) /
          (pcount (familyLanguage 1) n : ℝ))
      atTop (𝓝 0) := by
  let c : ℕ := E.ncard
  have hc : Tendsto (fun n : ℕ => (c : ℝ) / n) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hupperLim :
      Tendsto
        (fun n : ℕ => 2 *
          (((Nat.sqrt n : ℝ) + 1) / n + (c : ℝ) / n))
        atTop (𝓝 0) := by
    simpa using (tendsto_sparseSqrt_add_one_div.add hc).const_mul 2
  apply squeeze_zero'
    (g := fun n : ℕ => 2 *
      (((Nat.sqrt n : ℝ) + 1) / n + (c : ℝ) / n))
  · exact Filter.Eventually.of_forall fun n => ratio_nonneg _ _ n
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hden : (n : ℝ) / 2 ≤ (pcount (familyLanguage 1) n : ℝ) := by
      calc
        (n : ℝ) / 2 ≤ (pcount evenNaturals n : ℝ) := pcount_even_lower n
        _ ≤ (pcount (familyLanguage 1) n : ℝ) := by
          exact_mod_cast pcount_mono
            (by rw [familyLanguage_one]; exact Set.subset_union_right) n
    have hnumNat :
        pcount ((squareCore ∪ E) ∩ familyLanguage 1) n ≤
          Nat.sqrt n + 1 + c := by
      calc
        pcount ((squareCore ∪ E) ∩ familyLanguage 1) n ≤
            pcount (squareCore ∪ E) n :=
          pcount_mono Set.inter_subset_left n
        _ ≤ pcount squareCore n + pcount E n := pcount_union_le _ _ _
        _ ≤ (Nat.sqrt n + 1) + c := by
          apply Nat.add_le_add
          · rw [pcount_squareCore]
            exact count_sparseSquare_le_sqrt_add_one n
          · exact pcount_le_ncard_of_finite hE n
    have hnum :
        (pcount ((squareCore ∪ E) ∩ familyLanguage 1) n : ℝ) ≤
          (Nat.sqrt n : ℝ) + 1 + c := by exact_mod_cast hnumNat
    have hdenPos : 0 < (pcount (familyLanguage 1) n : ℝ) :=
      lt_of_lt_of_le (by positivity : 0 < (n : ℝ) / 2) hden
    calc
      (pcount ((squareCore ∪ E) ∩ familyLanguage 1) n : ℝ) /
          (pcount (familyLanguage 1) n : ℝ)
        ≤ ((Nat.sqrt n : ℝ) + 1 + c) /
            (pcount (familyLanguage 1) n : ℝ) :=
          div_le_div_of_nonneg_right hnum hdenPos.le
      _ ≤ ((Nat.sqrt n : ℝ) + 1 + c) / ((n : ℝ) / 2) := by
          apply div_le_div_of_nonneg_left
          · positivity
          · positivity
          · exact hden
      _ = 2 * (((Nat.sqrt n : ℝ) + 1) / n + (c : ℝ) / n) := by
          field_simp
  · exact hupperLim

 theorem relativeUpperDensity_zero_of_eventual_square
    {input output : Stage3Case024.Stream}
    (h : GenLimit.NovelGeneratesInLimit input output squareCore) :
    relativeUpperDensity (GenLimit.GeneratorFirst input output)
      (familyLanguage 1) = 0 := by
  let D := GenLimit.GeneratorFirst input output
  let E := D \ squareCore
  have hE : E.Finite := generatorFirst_diff_finite_of_eventual h
  have hsub : D ⊆ squareCore ∪ E := by
    intro x hx
    by_cases hxcore : x ∈ squareCore
    · exact Or.inl hxcore
    · exact Or.inr ⟨hx, hxcore⟩
  have hratio :
      ∀ n,
        (pcount (D ∩ familyLanguage 1) n : ℝ) /
            (pcount (familyLanguage 1) n : ℝ) ≤
          (pcount ((squareCore ∪ E) ∩ familyLanguage 1) n : ℝ) /
            (pcount (familyLanguage 1) n : ℝ) := by
    intro n
    apply div_le_div_of_nonneg_right
    · exact_mod_cast pcount_mono (Set.inter_subset_inter_left _ hsub) n
    · positivity
  have htendsto :
      Tendsto
        (fun n : ℕ =>
          (pcount ((squareCore ∪ E) ∩ familyLanguage 1) n : ℝ) /
            (pcount (familyLanguage 1) n : ℝ))
        atTop (𝓝 0) := finite_core_ratio_tendsto_zero E hE
  have hzero :
      Tendsto
        (fun n : ℕ =>
          (pcount (D ∩ familyLanguage 1) n : ℝ) /
            (pcount (familyLanguage 1) n : ℝ))
        atTop (𝓝 0) := by
    apply squeeze_zero' (g := fun n : ℕ =>
      (pcount ((squareCore ∪ E) ∩ familyLanguage 1) n : ℝ) /
        (pcount (familyLanguage 1) n : ℝ))
    · exact Filter.Eventually.of_forall fun n => ratio_nonneg D (familyLanguage 1) n
    · exact Filter.Eventually.of_forall hratio
    · exact htendsto
  exact hzero.limsup_eq

end Stage3Case024Proof

namespace Stage3Case024Proof

open Stage3Case024
open GenLimit

noncomputable def freshGenerator
    (K : Stage3Case024.Language) (hK : K.Infinite) : OnlineGenerator :=
  fun _ input output =>
    Classical.choose
      (hK.exists_notMem_finset
        ((Finset.univ.image input) ∪ (Finset.univ.image output)))

 theorem freshGenerator_spec
    (K : Stage3Case024.Language) (hK : K.Infinite)
    (t : ℕ) (input : Fin (t + 1) → ℕ) (output : Fin t → ℕ) :
    freshGenerator K hK t input output ∈ K ∧
      freshGenerator K hK t input output ∉ Finset.univ.image input ∧
      freshGenerator K hK t input output ∉ Finset.univ.image output := by
  simpa [freshGenerator] using
    Classical.choose_spec
      (hK.exists_notMem_finset
        ((Finset.univ.image input) ∪ (Finset.univ.image output)))

noncomputable def runGenerator
    (gen : OnlineGenerator) (input : Stage3Case024.Stream) (t : ℕ) : ℕ :=
  gen t (fun i => input i) (fun i => runGenerator gen input i)
termination_by t

 theorem runGenerator_follows (gen : OnlineGenerator)
    (input : Stage3Case024.Stream) :
    Follows gen input (runGenerator gen input) := by
  intro t
  rw [runGenerator]

 theorem freshGenerator_run_novel
    (K : Stage3Case024.Language) (hK : K.Infinite)
    (input : Stage3Case024.Stream) :
    GenLimit.NovelGeneratesInLimit input
      (runGenerator (freshGenerator K hK) input) K := by
  refine ⟨0, ?_⟩
  intro t _
  let output := runGenerator (freshGenerator K hK) input
  have hspec := freshGenerator_spec K hK t
    (fun i => input i) (fun i => output i)
  have heq : output t = freshGenerator K hK t
      (fun i => input i) (fun i => output i) := by
    dsimp [output]
    rw [runGenerator]
  change output t ∈ K ∧ output t ∉ GenLimit.sample input (t + 1) ∧
    ∀ s, s < t → output s ≠ output t
  rw [heq]
  refine ⟨hspec.1, ?_, ?_⟩
  · intro hsample
    rw [GenLimit.mem_sample_iff] at hsample
    obtain ⟨s, hs, hvalue⟩ := hsample
    apply hspec.2.1
    rw [Finset.mem_image]
    exact ⟨⟨s, hs⟩, Finset.mem_univ _, hvalue⟩
  · intro s hs hrepeat
    apply hspec.2.2
    rw [Finset.mem_image]
    exact ⟨⟨s, hs⟩, Finset.mem_univ _, hrepeat⟩

 theorem family_globallyFeasible (r : ℕ) :
    GloballyFeasible (fun i : Fin r => familyLanguage i) := by
  let gen := freshGenerator squareCore squareCore_infinite
  refine ⟨gen, ?_⟩
  intro input _
  let output := runGenerator gen input
  refine ⟨output, runGenerator_follows gen input, ?_⟩
  intro j
  obtain ⟨T, hT⟩ := freshGenerator_run_novel squareCore squareCore_infinite input
  refine ⟨T, ?_⟩
  intro t ht
  obtain ⟨hcore, hfresh, hnovel⟩ := hT t ht
  exact ⟨squareCore_subset_familyLanguage j hcore, hfresh, hnovel⟩

end Stage3Case024Proof
