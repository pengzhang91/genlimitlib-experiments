import Stage3Model
import GenLimit.Paper39_DenseGeneration.Patient.Main
import GenLimit.Paper17_InfiniteContamination.FiniteContaminationSufficiency

open Stage3Case025

namespace Case025

open GenLimit
open GenLimit.PatientMachine

theorem sample_eq_of_eq_prefix {stream₁ stream₂ : ℕ → ℕ} {t : ℕ}
    (h : ∀ s, s < t → stream₁ s = stream₂ s) :
    GenLimit.sample stream₁ t = GenLimit.sample stream₂ t := by
  ext x
  simp only [GenLimit.mem_sample_iff]
  constructor <;> rintro ⟨s, hs, rfl⟩
  · exact ⟨s, hs, (h s hs).symm⟩
  · exact ⟨s, hs, h s hs⟩

theorem consistent_congr {C : GenLimit.LanguageFamily}
    {stream₁ stream₂ : ℕ → ℕ} {t i : ℕ}
    (h : ∀ s, s < t → stream₁ s = stream₂ s) :
    GenLimit.Consistent C stream₁ t i ↔ GenLimit.Consistent C stream₂ t i := by
  simp only [GenLimit.Consistent, sample_eq_of_eq_prefix h]

theorem recursiveCritical_congr {C : GenLimit.LanguageFamily}
    {stream₁ stream₂ : ℕ → ℕ} {t i : ℕ}
    (h : ∀ s, s < t → stream₁ s = stream₂ s) :
    GenLimit.RecursiveCritical C stream₁ t i ↔
      GenLimit.RecursiveCritical C stream₂ t i := by
  induction i using Nat.strong_induction_on with
  | h i ih =>
      cases i with
      | zero =>
          simpa [GenLimit.RecursiveCritical] using
            consistent_congr (C := C) (i := 0) h
      | succ i =>
          simp only [GenLimit.RecursiveCritical]
          rw [consistent_congr h]
          constructor
          · rintro ⟨hc, hall⟩
            exact ⟨hc, fun j hj hjcrit => hall j hj ((ih j (Nat.lt_succ_of_le hj)).mpr hjcrit)⟩
          · rintro ⟨hc, hall⟩
            exact ⟨hc, fun j hj hjcrit => hall j hj ((ih j (Nat.lt_succ_of_le hj)).mp hjcrit)⟩

theorem processRound_congr (O : GenLimit.OracleFamily)
    {stream₁ stream₂ : ℕ → ℕ} {t : ℕ} {old : State}
    (h : ∀ s, s < t + 1 → stream₁ s = stream₂ s) :
    processRound O stream₁ t old = processRound O stream₂ t old := by
  classical
  have hs : GenLimit.sample stream₁ (t + 1) = GenLimit.sample stream₂ (t + 1) :=
    sample_eq_of_eq_prefix h
  have hc : ∀ i, GenLimit.Consistent O.language stream₁ (t + 1) i ↔
      GenLimit.Consistent O.language stream₂ (t + 1) i :=
    fun i => consistent_congr h
  have hprefix : ∀ s, s < t → stream₁ s = stream₂ s :=
    fun s hslt => h s (lt_trans hslt (Nat.lt_succ_self t))
  have hr0 : ∀ i, GenLimit.RecursiveCritical O.language stream₁ t i ↔
      GenLimit.RecursiveCritical O.language stream₂ t i :=
    fun i => recursiveCritical_congr hprefix
  have hr1 : ∀ i, GenLimit.RecursiveCritical O.language stream₁ (t + 1) i ↔
      GenLimit.RecursiveCritical O.language stream₂ (t + 1) i :=
    fun i => recursiveCritical_congr h
  have hconsistent (scope : ℕ) :
      consistentIndices O.language stream₁ (t + 1) scope =
        consistentIndices O.language stream₂ (t + 1) scope := by
    ext i
    simp only [mem_consistentIndices]
    exact and_congr_right (fun _ => hc i)
  have hcritical (scope : ℕ) :
      criticalIndices O.language stream₁ (t + 1) scope =
        criticalIndices O.language stream₂ (t + 1) scope := by
    ext i
    simp only [mem_criticalIndices]
    exact and_congr_right (fun _ => hr1 i)
  have hsurviving (scope : ℕ) :
      survivingCriticalIndices O.language stream₁ t scope =
        survivingCriticalIndices O.language stream₂ t scope := by
    ext i
    simp only [mem_survivingCriticalIndices]
    exact and_congr_right (fun _ => and_congr (hr0 i) (hr1 i))
  have hhighest (scope fallback : ℕ) :
      highestCritical O.language stream₁ (t + 1) scope fallback =
        highestCritical O.language stream₂ (t + 1) scope fallback := by
    unfold highestCritical
    rw [hcritical]
  have hsurvivor (scope fallback : ℕ) :
      highestSurvivor O.language stream₁ t scope fallback =
        highestSurvivor O.language stream₂ t scope fallback := by
    unfold highestSurvivor
    rw [hsurviving]
  have hlowscope (scope fallback : ℕ) :
      lowestConsistentInScope O.language stream₁ (t + 1) scope fallback =
        lowestConsistentInScope O.language stream₂ (t + 1) scope fallback := by
    unfold lowestConsistentInScope
    rw [hconsistent]
  have hlowglobal (fallback : ℕ) :
      lowestConsistent O.language stream₁ (t + 1) fallback =
        lowestConsistent O.language stream₂ (t + 1) fallback := by
    unfold lowestConsistent GenLimit.Consistent
    rw [hs]
  have hstable :
      stableDecision O.language stream₁ t old =
        stableDecision O.language stream₂ t old := by
    unfold stableDecision
    split
    · simp only [hhighest]
    · rfl
  have hbacktrack :
      backtrackDecision O.language stream₁ t old =
        backtrackDecision O.language stream₂ t old := by
    unfold backtrackDecision
    rw [hconsistent, hsurviving]
    simp only [hsurvivor, hlowscope, hlowglobal]
    simp only [GenLimit.Consistent, hs]
  have hdecide :
      GenLimit.PatientMachine.decide O.language stream₁ t old =
        GenLimit.PatientMachine.decide O.language stream₂ t old := by
    unfold GenLimit.PatientMachine.decide
    rw [hc old.focus]
    split
    · exact hstable
    · exact hbacktrack
  have hleast (used : Finset ℕ) (focus : ℕ) :
      leastAvailable O.language O.infinite' stream₁ (t + 1) used focus =
        leastAvailable O.language O.infinite' stream₂ (t + 1) used focus := by
    apply Nat.le_antisymm
    · apply leastAvailable_minimal
      have havail := leastAvailable_spec O.language O.infinite'
        stream₂ (t + 1) used focus
      simpa only [Available, hs] using havail
    · apply leastAvailable_minimal
      have havail := leastAvailable_spec O.language O.infinite'
        stream₁ (t + 1) used focus
      simpa only [Available, hs] using havail
  simp only [processRound, hdecide, hleast]

theorem run_congr (O : GenLimit.OracleFamily)
    {stream₁ stream₂ : ℕ → ℕ} : ∀ t,
    (∀ s, s < t → stream₁ s = stream₂ s) →
      run O stream₁ t = run O stream₂ t := by
  intro t h
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [run_succ, run_succ, ih (fun s hs => h s (Nat.lt.step hs))]
      exact processRound_congr O h

theorem output_congr (O : GenLimit.OracleFamily)
    {stream₁ stream₂ : ℕ → ℕ} {t : ℕ}
    (h : ∀ s, s < t + 1 → stream₁ s = stream₂ s) :
    output O stream₁ t = output O stream₂ t := by
  unfold output
  rw [run_congr O (t + 1) h]

end Case025

namespace Case025

open Filter
open scoped Topology
open GenLimit
open GenLimit.PatientMachine
open GenLimit.PatientScope

noncomputable def baseOracle (family : ℕ → Stage3Case025.Language)
    (hinfinite : ∀ i, (family i).Infinite) : GenLimit.OracleFamily where
  language := family
  infinite' := hinfinite
  query i x := by classical exact if x ∈ family i then true else false
  query_spec i x := by classical simp

abbrev ExpansionCode := ℕ × ℕ

def expansionCode (n : ℕ) : ExpansionCode := Nat.unpair n

def encodeExpansionCode (data : ExpansionCode) : ℕ := Nat.pair data.1 data.2

@[simp] theorem expansionCode_encode (data : ExpansionCode) :
    expansionCode (encodeExpansionCode data) = data := by
  simp [expansionCode, encodeExpansionCode, Nat.unpair_pair]

noncomputable def expandedLanguage (family : ℕ → Stage3Case025.Language)
    (n : ℕ) : Stage3Case025.Language :=
  family (expansionCode n).1 ∪
    (Finset.equivBitIndices (expansionCode n).2 : Set ℕ)

noncomputable def expandedOracle (family : ℕ → Stage3Case025.Language)
    (hinfinite : ∀ i, (family i).Infinite) : GenLimit.OracleFamily where
  language := expandedLanguage family
  infinite' n := (hinfinite (expansionCode n).1).mono Set.subset_union_left
  query n x := by classical exact if x ∈ expandedLanguage family n then true else false
  query_spec n x := by classical simp

noncomputable def prefixStream (t : ℕ) (history : Fin (t + 1) → ℕ) : ℕ → ℕ :=
  fun n => if h : n < t + 1 then history ⟨n, h⟩ else 0

noncomputable def patientOnline (O : GenLimit.OracleFamily) : OnlineGenerator :=
  fun t history _ => output O (prefixStream t history) t

theorem patientOnline_follows (O : GenLimit.OracleFamily) (input : Stream) :
    Follows (patientOnline O) input (output O input) := by
  intro t
  symm
  apply output_congr
  intro s hs
  simp [patientOnline, prefixStream, hs]

 theorem exists_expansion_index
    (family : ℕ → Stage3Case025.Language) {i : ℕ} {input : Stream}
    (hcover : family i ⊆ Set.range input)
    (hnoise : GenLimit.Generic.FinitelyManyViolations input (fun x => x ∈ family i)) :
    ∃ j, GenLimit.Presents input (expandedLanguage family j) ∧
      (expandedLanguage family j \ family i).Finite := by
  let noise : Set ℕ := Set.range input \ family i
  have hnoiseFinite : noise.Finite := by
    change (GenLimit.InfiniteContamination.displayedNoise input (family i)).Finite
    exact GenLimit.InfiniteContamination.displayedNoise_finite hnoise
  let data : ExpansionCode :=
    (i, Finset.equivBitIndices.symm hnoiseFinite.toFinset)
  let j := encodeExpansionCode data
  refine ⟨j, ?_, ?_⟩
  · change Set.range input = expandedLanguage family j
    unfold expandedLanguage
    simp only [j, data, expansionCode_encode, Equiv.apply_symm_apply]
    rw [Set.Finite.coe_toFinset hnoiseFinite]
    ext x
    constructor
    · intro hx
      by_cases hxi : x ∈ family i
      · exact Or.inl hxi
      · exact Or.inr ⟨hx, hxi⟩
    · rintro (hx | hx)
      · exact hcover hx
      · exact hx.1
  · unfold expandedLanguage
    simp only [j, data, expansionCode_encode, Equiv.apply_symm_apply]
    rw [Set.Finite.coe_toFinset hnoiseFinite]
    apply hnoiseFinite.subset
    intro x hx
    exact hx.1.resolve_left hx.2

 theorem novel_transfer
    {input output : Stream} {L E : Set ℕ}
    (hpresents : GenLimit.Presents input E)
    (hextra : (E \ L).Finite)
    (hnovel : GenLimit.NovelGeneratesInLimit input output E) :
    GenLimit.NovelGeneratesInLimit input output L := by
  classical
  obtain ⟨T, hT⟩ := hnovel
  obtain ⟨S, hS⟩ := GenLimit.Generic.finset_eventually_subset_sample
    (stream := input) (L := Set.range input) rfl hextra.toFinset (by
      intro x hx
      rw [hpresents]
      exact ((Set.Finite.mem_toFinset hextra).mp hx).1)
  refine ⟨max T S, ?_⟩
  intro t ht
  have htT : T ≤ t := (Nat.le_max_left _ _).trans ht
  have htS : S ≤ t := (Nat.le_max_right _ _).trans ht
  obtain ⟨houtE, hfresh, hdistinct⟩ := hT t htT
  refine ⟨?_, hfresh, hdistinct⟩
  by_contra houtL
  have hbad : output t ∈ hextra.toFinset :=
    (Set.Finite.mem_toFinset hextra).mpr ⟨houtE, houtL⟩
  have hseenS := hS hbad
  have hseenT := GenLimit.Generic.sample_mono htS hseenS
  have hseenSucc := GenLimit.Generic.sample_mono (Nat.le_succ t) hseenT
  exact hfresh (by simpa [GenLimit.Generic.sample, GenLimit.sample] using hseenSucc)

 theorem prefixCount_le_add_diff {A B : Set ℕ}
    (hfinite : (A \ B).Finite) (n : ℕ) :
    prefixCount A n ≤ prefixCount B n + hfinite.toFinset.card := by
  classical
  let a := prefixFinset A n
  let b := prefixFinset B n
  let d := prefixFinset (A \ B) n
  have hsub : a ⊆ b ∪ d := by
    intro x hx
    have hx' := mem_prefixFinset.mp hx
    by_cases hxB : x ∈ B
    · exact Finset.mem_union_left _ (mem_prefixFinset.mpr ⟨hx'.1, hxB⟩)
    · exact Finset.mem_union_right _ (mem_prefixFinset.mpr ⟨hx'.1, hx'.2, hxB⟩)
  have hd : d.card ≤ hfinite.toFinset.card := by
    apply Finset.card_le_card
    intro x hx
    exact Set.Finite.mem_toFinset hfinite |>.2 (mem_prefixFinset.mp hx).2
  exact (Finset.card_le_card hsub).trans
    ((Finset.card_union_le b d).trans (Nat.add_le_add_left hd _))

 theorem liminf_le_of_vanishing_error
    (source target error : ℕ → ℝ)
    (hsource0 : ∀ n, 0 ≤ source n) (hsource1 : ∀ n, source n ≤ 1)
    (htarget0 : ∀ n, 0 ≤ target n) (htarget1 : ∀ n, target n ≤ 1)
    (herror : Tendsto error atTop (𝓝 0))
    (hcompare : ∀ᶠ n in atTop, source n ≤ target n + error n) :
    liminf source atTop ≤ liminf target atTop := by
  apply (le_liminf_iff
    (isCoboundedUnder_ge_of_le atTop htarget1)
    (isBoundedUnder_of ⟨0, htarget0⟩)).2
  intro y hy
  obtain ⟨r, hyr, hr⟩ := exists_between hy
  have hrEventually : ∀ᶠ n in atTop, r < source n :=
    eventually_lt_of_lt_liminf hr (isBoundedUnder_of ⟨0, hsource0⟩)
  have heEventually : ∀ᶠ n in atTop, error n < r - y := by
    exact herror.eventually (Iio_mem_nhds (sub_pos.mpr hyr))
  filter_upwards [hrEventually, heEventually, hcompare] with n hn he hc
  linarith

 theorem relative_density_finite_expansion
    (G L E : Set ℕ) (hL : L.Infinite) (hLE : L ⊆ E)
    (hfinite : (E \ L).Finite) :
    relativeLowerDensity (G ∩ E) E ≤ relativeLowerDensity (G ∩ L) L := by
  let source := fun n : ℕ =>
    (prefixCount (G ∩ E) n : ℝ) / (prefixCount E n : ℝ)
  let target := fun n : ℕ =>
    (prefixCount (G ∩ L) n : ℝ) / (prefixCount L n : ℝ)
  have hdiff : ((G ∩ E) \ (G ∩ L)).Finite := by
    apply hfinite.subset
    intro x hx
    exact ⟨hx.1.2, fun hxL => hx.2 ⟨hx.1.1, hxL⟩⟩
  let error := fun n : ℕ =>
    (hdiff.toFinset.card : ℝ) / (prefixCount L n : ℝ)
  have hden : Tendsto (fun n => (prefixCount L n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_prefixCount_atTop hL)
  have herror : Tendsto error atTop (𝓝 0) := by
    exact tendsto_const_nhds.div_atTop hden
  have hsource0 : ∀ n, 0 ≤ source n := fun n => div_nonneg (by positivity) (by positivity)
  have htarget0 : ∀ n, 0 ≤ target n := fun n => div_nonneg (by positivity) (by positivity)
  have hsource1 : ∀ n, source n ≤ 1 := by
    intro n
    by_cases hn : prefixCount E n = 0
    · simp [source, hn]
    · simp only [source]
      rw [div_le_one (by positivity)]
      exact_mod_cast prefixCount_mono Set.inter_subset_right n
  have htarget1 : ∀ n, target n ≤ 1 := by
    intro n
    by_cases hn : prefixCount L n = 0
    · simp [target, hn]
    · simp only [target]
      rw [div_le_one (by positivity)]
      exact_mod_cast prefixCount_mono Set.inter_subset_right n
  have hcompare : ∀ᶠ n in atTop, source n ≤ target n + error n := by
    have hpos : ∀ᶠ n in atTop, 0 < prefixCount L n :=
      (tendsto_prefixCount_atTop hL).eventually (eventually_gt_atTop 0)
    filter_upwards [hpos] with n hn
    have hnL : (0 : ℝ) < prefixCount L n := by exact_mod_cast hn
    have hnE : (0 : ℝ) < prefixCount E n := by
      exact_mod_cast lt_of_lt_of_le hn (prefixCount_mono hLE n)
    have hd : prefixCount (G ∩ E) n ≤
        prefixCount (G ∩ L) n + hdiff.toFinset.card :=
      prefixCount_le_add_diff hdiff n
    have hdenom := prefixCount_mono hLE n
    have hdR : (prefixCount (G ∩ E) n : ℝ) ≤
        prefixCount (G ∩ L) n + hdiff.toFinset.card := by exact_mod_cast hd
    have hdenomR : (prefixCount L n : ℝ) ≤ prefixCount E n := by exact_mod_cast hdenom
    dsimp [source, target, error]
    rw [← add_div]
    apply (div_le_div_iff₀ hnE hnL).2
    exact mul_le_mul hdR hdenomR (by positivity) (by positivity)
  unfold relativeLowerDensity
  exact liminf_le_of_vanishing_error source target error
    hsource0 hsource1 htarget0 htarget1 herror hcompare

 theorem stage3_complete : Stage3Case025.MainClaim := by
  intro family hinfinite
  let O := expandedOracle family hinfinite
  refine ⟨patientOnline O, ?_⟩
  intro i input hpresentation
  obtain ⟨j, hpresents, hextra⟩ :=
    exists_expansion_index family hpresentation.1 hpresentation.2
  let out := output O input
  have hrun := patientScope_generation_and_lowerDensity O input (z := j) hpresents
  refine ⟨out, patientOnline_follows O input, ?_, ?_⟩
  · have hnovelE : GenLimit.NovelGeneratesInLimit input out (O.language j) := by
      obtain ⟨⟨T, hT⟩, -⟩ := hrun
      refine ⟨T, ?_⟩
      intro t ht
      obtain ⟨hmem, hfresh, hdistinct⟩ := hT t ht
      refine ⟨hmem, ?_, hdistinct⟩
      intro hsamp
      rw [GenLimit.mem_sample_iff] at hsamp
      obtain ⟨s, hs, heq⟩ := hsamp
      exact (hfresh s (Nat.le_of_lt_succ hs)) heq
    exact novel_transfer hpresents hextra hnovelE
  · have hdE : (1 / 2 : ℝ) ≤ relativeLowerDensity
        (GenLimit.GeneratorFirst input out ∩ O.language j) (O.language j) := by
      simpa [out, patientLowerDensity] using hrun.2
    have hsubset : family i ⊆ O.language j := by
      change family i ⊆ expandedLanguage family j
      rw [← hpresents]
      exact hpresentation.1
    exact hdE.trans (relative_density_finite_expansion
      (GenLimit.GeneratorFirst input out) (family i) (O.language j)
      (hinfinite i) hsubset hextra)

end Case025

theorem stage3_result : Stage3Case025.MainClaim := by
  exact Case025.stage3_complete
