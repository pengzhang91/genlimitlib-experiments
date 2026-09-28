import Stage3Model
import GenLimit.Paper17_InfiniteContamination.SharedVanishingPresentation
import Mathlib.Tactic

open Filter MeasureTheory
open scoped Topology

namespace Case024

open Stage3Case024
open GenLimit
open GenLimit.InfiniteContamination

noncomputable local instance : DecidablePred SparseSquare := Classical.decPred _

abbrev core : Set ℕ := {n | SparseSquare n}

def marker (k : ℕ) : ℕ := sparseBetweenSquares k

def initialMarkers (i : ℕ) : Set ℕ := {n | ∃ k < i, marker k = n}

def targetFamily {r : ℕ} (i : Fin r) : Stage3Case024.Language :=
  if i.1 + 1 = r then Set.univ else core ∪ initialMarkers i.1

lemma core_infinite : core.Infinite := by
  have hinj : Function.Injective (fun k : ℕ => k * k) := by
    intro a b h
    nlinarith
  apply (Set.infinite_range_of_injective hinj).mono
  rintro _ ⟨k, rfl⟩
  exact sparseSquare_mul_self k

lemma marker_nonsquare (k : ℕ) : marker k ∉ core :=
  sparseBetweenSquares_nonsquare k

lemma marker_injective : Function.Injective marker :=
  sparseBetweenSquares_strictMono.injective

lemma initialMarkers_mono {i j : ℕ} (hij : i ≤ j) :
    initialMarkers i ⊆ initialMarkers j := by
  rintro x ⟨k, hk, rfl⟩
  exact ⟨k, hk.trans_le hij, rfl⟩

lemma marker_mem_initialMarkers {i j : ℕ} (hij : i < j) :
    marker i ∈ initialMarkers j :=
  ⟨i, hij, rfl⟩

lemma marker_not_mem_initialMarkers (i : ℕ) :
    marker i ∉ initialMarkers i := by
  rintro ⟨k, hk, heq⟩
  exact (Nat.ne_of_lt hk) (marker_injective heq)

lemma family_core_subset {r : ℕ} (i : Fin r) : core ⊆ targetFamily i := by
  intro x hx
  simp only [targetFamily]
  split <;> simp_all

lemma family_infinite {r : ℕ} (i : Fin r) : (targetFamily i).Infinite :=
  core_infinite.mono (family_core_subset i)

def lastIndex (r : ℕ) (hr : 0 < r) : Fin r := ⟨r - 1, by omega⟩

lemma targetFamily_last {r : ℕ} (hr : 0 < r) :
    targetFamily (lastIndex r hr) = Set.univ := by
  rw [targetFamily, if_pos]
  change r - 1 + 1 = r
  omega

lemma targetFamily_strictlyNested {r : ℕ} :
    Stage3Case024.StrictlyNested (@targetFamily r) := by
  intro i j hij
  have hi_not_last : i.1 + 1 ≠ r := by omega
  by_cases hj_last : j.1 + 1 = r
  · change (if i.1 + 1 = r then Set.univ else core ∪ initialMarkers i.1) ⊂
      (if j.1 + 1 = r then Set.univ else core ∪ initialMarkers j.1)
    simp only [hi_not_last, hj_last, if_false, if_true]
    refine Set.ssubset_univ_iff.mpr ?_
    intro heq
    have hm : marker i.1 ∈ core ∪ initialMarkers i.1 := by
      rw [heq]
      trivial
    rcases hm with hm | hm
    · exact marker_nonsquare i.1 hm
    · exact marker_not_mem_initialMarkers i.1 hm
  · change (if i.1 + 1 = r then Set.univ else core ∪ initialMarkers i.1) ⊂
      (if j.1 + 1 = r then Set.univ else core ∪ initialMarkers j.1)
    simp only [hi_not_last, hj_last, if_false]
    refine Set.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
    · exact Set.union_subset_union_right _ (initialMarkers_mono hij.le)
    · intro heq
      have hm : marker i.1 ∈ core ∪ initialMarkers j.1 :=
        Set.mem_union_right _ (marker_mem_initialMarkers hij)
      rw [← heq] at hm
      rcases hm with hm | hm
      · exact marker_nonsquare i.1 hm
      · exact marker_not_mem_initialMarkers i.1 hm

noncomputable def commonInput : Stream :=
  sparseMergePresentation core (Set.univ \ core) core_infinite

lemma commonInput_injective : Function.Injective commonInput := by
  apply sparseMergePresentation_injective core_infinite
  exact Set.disjoint_sdiff_right

lemma commonInput_range : Set.range commonInput = Set.univ := by
  rw [commonInput, range_sparseMergePresentation core_infinite]
  exact Set.union_diff_cancel (Set.subset_univ _)

lemma commonInput_legal_of_core_subset (K : Stage3Case024.Language) (hcore : core ⊆ K)
    (hK : K.Infinite) : Legal commonInput K := by
  refine ⟨hK, commonInput_injective, ?_, ?_⟩
  · rw [GenLimit.InfiniteContamination.NoOmissions, commonInput_range]
    exact Set.subset_univ _
  · exact sparseMergePresentation_vanishingNoise_of_core_subset core_infinite hcore

lemma commonInput_legal_family {r : ℕ} (i : Fin r) :
    Legal commonInput (targetFamily i) :=
  commonInput_legal_of_core_subset (targetFamily i)
    (family_core_subset i) (family_infinite i)

lemma commonInput_legal_core : Legal commonInput core :=
  commonInput_legal_of_core_subset _ (fun _ h => h) core_infinite

lemma commonInput_legal_univ : Legal commonInput Set.univ :=
  commonInput_legal_of_core_subset Set.univ (Set.subset_univ _) Set.infinite_univ

lemma prefixCount_univ (n : ℕ) :
    GenLimit.PatientScope.prefixCount (Set.univ : Set ℕ) n = n := by
  simp [GenLimit.PatientScope.prefixCount, GenLimit.PatientScope.prefixFinset]

lemma prefixCount_core (n : ℕ) :
    GenLimit.PatientScope.prefixCount core n = Nat.count SparseSquare n := by
  classical
  rw [Nat.count_eq_card_filter_range]
  rfl

lemma prefixCount_mono {A B : Set ℕ} (h : A ⊆ B) (n : ℕ) :
    GenLimit.PatientScope.prefixCount A n ≤
      GenLimit.PatientScope.prefixCount B n := by
  classical
  unfold GenLimit.PatientScope.prefixCount GenLimit.PatientScope.prefixFinset
  apply Finset.card_le_card
  intro x hx
  simp only [Finset.mem_filter, Finset.mem_range] at hx ⊢
  exact ⟨hx.1, h hx.2⟩

lemma prefixCount_union_le (A B : Set ℕ) (n : ℕ) :
    GenLimit.PatientScope.prefixCount (A ∪ B) n ≤
      GenLimit.PatientScope.prefixCount A n +
        GenLimit.PatientScope.prefixCount B n := by
  classical
  unfold GenLimit.PatientScope.prefixCount GenLimit.PatientScope.prefixFinset
  simpa [Finset.filter_or] using
    Finset.card_union_le ((Finset.range n).filter (fun x => x ∈ A))
      ((Finset.range n).filter (fun x => x ∈ B))

lemma prefixCount_finite_le (E : Set ℕ) (hE : E.Finite) (n : ℕ) :
    GenLimit.PatientScope.prefixCount E n ≤ hE.toFinset.card := by
  classical
  unfold GenLimit.PatientScope.prefixCount GenLimit.PatientScope.prefixFinset
  apply Finset.card_le_card
  intro x hx
  simp only [Finset.mem_filter, Finset.mem_range] at hx
  simpa using hx.2

lemma relativeUpperDensity_le_one
    (A K : Stage3Case024.Language) :
    relativeUpperDensity A K ≤ 1 := by
  unfold relativeUpperDensity
  apply limsup_le_of_le
  · exact isCoboundedUnder_le_of_le atTop (fun n => by positivity)
  · filter_upwards [] with n
    have hcount := prefixCount_mono
      (Set.inter_subset_right : A ∩ K ⊆ K) n
    by_cases hzero : GenLimit.PatientScope.prefixCount K n = 0
    · simp [hzero]
    · rw [div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hzero)]
      exact_mod_cast hcount

lemma generatorFirst_eventually_core_subset
    {input output : Stream} (hvalid : NovelGeneratesInLimit input output core) :
    ∃ E : Set ℕ, E.Finite ∧ GeneratorFirst input output ⊆ core ∪ E := by
  obtain ⟨T, hT⟩ := hvalid
  let E : Set ℕ := Set.range (fun i : Fin T => output i)
  refine ⟨E, Set.finite_range _, ?_⟩
  intro x hx
  obtain ⟨t, rfl, -⟩ := hx
  by_cases ht : T ≤ t
  · exact Set.mem_union_left _ (hT t ht).1
  · exact Set.mem_union_right _ ⟨⟨t, Nat.lt_of_not_ge ht⟩, rfl⟩

lemma relativeUpperDensity_generatorFirst_univ_eq_zero
    {input output : Stream} (hvalid : NovelGeneratesInLimit input output core) :
    relativeUpperDensity (GeneratorFirst input output) Set.univ = 0 := by
  obtain ⟨E, hE, hsubset⟩ := generatorFirst_eventually_core_subset hvalid
  let c : ℕ := hE.toFinset.card
  have hbound (n : ℕ) :
      GenLimit.PatientScope.prefixCount
          (GeneratorFirst input output ∩ (Set.univ : Set ℕ)) n ≤
        Nat.sqrt n + 1 + c := by
    calc
      GenLimit.PatientScope.prefixCount
          (GeneratorFirst input output ∩ (Set.univ : Set ℕ)) n
          ≤ GenLimit.PatientScope.prefixCount (core ∪ E) n :=
        prefixCount_mono (fun x hx => hsubset hx.1) n
      _ ≤ GenLimit.PatientScope.prefixCount core n +
          GenLimit.PatientScope.prefixCount E n := prefixCount_union_le core E n
      _ ≤ Nat.sqrt n + 1 + c := by
        rw [prefixCount_core]
        exact Nat.add_le_add
          (count_sparseSquare_le_sqrt_add_one n)
          (prefixCount_finite_le E hE n)
  have htendsto : Tendsto
      (fun n : ℕ => (((Nat.sqrt n : ℝ) + 1) + c) / (n : ℝ))
      atTop (𝓝 0) := by
    have hc : Tendsto (fun n : ℕ => (c : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    convert tendsto_sparseSqrt_add_one_div.add hc using 1 <;> simp [add_div]
  have hsqueeze : Tendsto
      (fun n : ℕ =>
        (GenLimit.PatientScope.prefixCount
          (GeneratorFirst input output ∩ (Set.univ : Set ℕ)) n : ℝ) /
          (GenLimit.PatientScope.prefixCount (Set.univ : Set ℕ) n : ℝ))
      atTop (𝓝 0) :=
    squeeze_zero
      (fun n => by positivity)
      (fun n => by
        rw [prefixCount_univ]
        apply div_le_div_of_nonneg_right
        · exact_mod_cast hbound n
        · positivity)
      htendsto
  exact hsqueeze.limsup_eq

noncomputable def freshChoice (K : Stage3Case024.Language) (hK : K.Infinite)
    (t : ℕ) (input : Fin (t + 1) → ℕ) (output : Fin t → ℕ) : ℕ :=
  Classical.choose (hK.exists_not_mem_finset
    ((Finset.univ.image input) ∪ (Finset.univ.image output)))

lemma freshChoice_spec (K : Stage3Case024.Language) (hK : K.Infinite)
    (t : ℕ) (input : Fin (t + 1) → ℕ) (output : Fin t → ℕ) :
    freshChoice K hK t input output ∈ K ∧
      freshChoice K hK t input output ∉ Finset.univ.image input ∧
      freshChoice K hK t input output ∉ Finset.univ.image output := by
  simpa [freshChoice] using
    Classical.choose_spec (hK.exists_not_mem_finset
      ((Finset.univ.image input) ∪ (Finset.univ.image output)))

noncomputable def freshGenerator
    (K : Stage3Case024.Language) (hK : K.Infinite) : OnlineGenerator :=
  freshChoice K hK

noncomputable def runGenerator (gen : OnlineGenerator) (input : Stream) : Stream
  | 0 => gen 0 (fun i => input i) (fun i => Fin.elim0 i)
  | t + 1 => gen (t + 1) (fun i => input i) (fun i => runGenerator gen input i)

lemma runGenerator_follows (gen : OnlineGenerator) (input : Stream) :
    Follows gen input (runGenerator gen input) := by
  intro t
  cases t with
  | zero =>
      simp only [runGenerator]
      congr 1
      funext i
      exact Fin.elim0 i
  | succ t => simp only [runGenerator]

lemma freshGenerator_valid
    (K : Stage3Case024.Language) (hK : K.Infinite) (input : Stream) :
    EventuallyFreshValidPath K input (runGenerator (freshGenerator K hK) input) := by
  refine ⟨0, ?_⟩
  intro t _
  have hs := freshChoice_spec K hK t (fun i => input i)
    (fun i => runGenerator (freshGenerator K hK) input i)
  have hrun := runGenerator_follows (freshGenerator K hK) input t
  refine ⟨?_, ?_, ?_⟩
  · rw [hrun]
    exact hs.1
  · intro hx
    rw [GenLimit.mem_sample_iff] at hx
    obtain ⟨s, hslt, heq⟩ := hx
    apply hs.2.1
    refine Finset.mem_image.mpr ⟨⟨s, hslt⟩, Finset.mem_univ _, ?_⟩
    change runGenerator (freshGenerator K hK) input t =
      freshChoice K hK t (fun i => input i)
        (fun i => runGenerator (freshGenerator K hK) input i) at hrun
    exact heq.trans hrun
  · intro s hslt heq
    apply hs.2.2
    refine Finset.mem_image.mpr ⟨⟨s, hslt⟩, Finset.mem_univ _, ?_⟩
    change runGenerator (freshGenerator K hK) input t =
      freshChoice K hK t (fun i => input i)
        (fun i => runGenerator (freshGenerator K hK) input i) at hrun
    exact heq.trans hrun

lemma globallyFeasible_family {r : ℕ} :
    GloballyFeasible (@targetFamily r) := by
  refine ⟨freshGenerator core core_infinite, ?_⟩
  intro input _
  refine ⟨runGenerator (freshGenerator core core_infinite) input,
    runGenerator_follows _ _, ?_⟩
  intro j
  obtain ⟨T, hT⟩ := freshGenerator_valid core core_infinite input
  refine ⟨T, ?_⟩
  intro t ht
  obtain ⟨hcore, hfresh, hnovel⟩ := hT t ht
  exact ⟨family_core_subset j hcore, hfresh, hnovel⟩

end Case024
