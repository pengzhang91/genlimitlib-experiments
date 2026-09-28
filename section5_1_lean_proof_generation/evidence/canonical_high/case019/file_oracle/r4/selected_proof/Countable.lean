import output.Helpers
import Mathlib

open Set Filter
open scoped Topology

namespace Stage3Case019Proof

open GenLimit
open GenLimit.Generic
open GenLimit.PatientScope
open GenLimit.InfiniteContamination

private theorem prefixCount_le_inter_add_finite
    {A K E : Set ℕ} (hAE : A ⊆ E) (hfinite : (E \ K).Finite) (n : ℕ) :
    prefixCount A n ≤
      prefixCount (A ∩ K) n + hfinite.toFinset.card := by
  classical
  unfold prefixCount
  calc
    (prefixFinset A n).card ≤
        (prefixFinset (A ∩ K) n ∪ hfinite.toFinset).card := by
      apply Finset.card_le_card
      intro x hx
      rw [Finset.mem_union]
      have hx' := mem_prefixFinset.mp hx
      by_cases hxK : x ∈ K
      · left
        exact mem_prefixFinset.mpr ⟨hx'.1, hx'.2, hxK⟩
      · right
        simpa using (show x ∈ E \ K from ⟨hAE hx'.2, hxK⟩)
    _ ≤ (prefixFinset (A ∩ K) n).card + hfinite.toFinset.card :=
      Finset.card_union_le _ _

private theorem relativeLowerDensity_inter_of_finite_extension
    {A K E : Set ℕ}
    (hK : K.Infinite) (hKE : K ⊆ E) (hAE : A ⊆ E)
    (hfinite : (E \ K).Finite)
    (hhalf : (1 / 2 : ℝ) ≤ relativeLowerDensity A E) :
    (1 / 2 : ℝ) ≤ relativeLowerDensity (A ∩ K) K := by
  let source : ℕ → ℝ := fun n =>
    (prefixCount A n : ℝ) / (prefixCount E n : ℝ)
  let target : ℕ → ℝ := fun n =>
    (prefixCount (A ∩ K) n : ℝ) / (prefixCount K n : ℝ)
  let error : ℕ → ℝ := fun n =>
    (hfinite.toFinset.card : ℝ) / (prefixCount K n : ℝ)
  have hKcount : Tendsto (prefixCount K) atTop atTop :=
    tendsto_prefixCount_atTop hK
  have herror : Tendsto error atTop (𝓝 0) := by
    exact tendsto_const_nhds.div_atTop
      (tendsto_natCast_atTop_atTop.comp hKcount)
  have hsource_nonneg : ∀ n, 0 ≤ source n := fun n => by
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have htarget_nonneg : ∀ n, 0 ≤ target n := fun n => by
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have htarget_le_one : ∀ n, target n ≤ 1 := by
    intro n
    change (prefixCount (A ∩ K) n : ℝ) / prefixCount K n ≤ 1
    by_cases hn : prefixCount K n = 0
    · simp [hn]
    · have hnpos : (0 : ℝ) < prefixCount K n := by
        exact_mod_cast Nat.pos_of_ne_zero hn
      rw [div_le_one hnpos]
      exact_mod_cast prefixCount_mono Set.inter_subset_right n
  rw [relativeLowerDensity] at hhalf ⊢
  change (1 / 2 : ℝ) ≤ liminf target atTop
  apply (le_liminf_iff
    (h₁ := isCoboundedUnder_ge_of_le atTop htarget_le_one)
    (h₂ := isBoundedUnder_of ⟨0, htarget_nonneg⟩)).2
  intro y hy
  let delta : ℝ := ((1 / 2 : ℝ) - y) / 2
  have hdelta : 0 < delta := by
    dsimp [delta]
    linarith
  have hydelta : y + delta < (1 / 2 : ℝ) := by
    dsimp [delta]
    linarith
  have hsourceBound : IsBoundedUnder (fun x₁ x₂ : ℝ => x₁ ≥ x₂) atTop source :=
    isBoundedUnder_of ⟨0, hsource_nonneg⟩
  have hsourceEventually : ∀ᶠ n in atTop, y + delta < source n := by
    apply eventually_lt_of_lt_liminf _ hsourceBound
    exact hydelta.trans_le hhalf
  have herrorEventually : ∀ᶠ n in atTop, error n < delta := by
    have : ∀ᶠ n in atTop, error n ∈ Set.Iio delta :=
      herror.eventually (isOpen_Iio.mem_nhds hdelta)
    exact this
  have hpositiveEventually : ∀ᶠ n in atTop, 0 < prefixCount K n :=
    hKcount.eventually (eventually_gt_atTop 0)
  filter_upwards [hsourceEventually, herrorEventually, hpositiveEventually]
    with n hsrc herr hn
  have hnR : (0 : ℝ) < prefixCount K n := by exact_mod_cast hn
  have hdenom : (prefixCount K n : ℝ) ≤ prefixCount E n := by
    exact_mod_cast prefixCount_mono hKE n
  have hnum := prefixCount_le_inter_add_finite hAE hfinite n
  have hnumR :
      (prefixCount A n : ℝ) ≤
        prefixCount (A ∩ K) n + hfinite.toFinset.card := by
    exact_mod_cast hnum
  have hsource_le :
      source n ≤
        ((prefixCount (A ∩ K) n : ℝ) + hfinite.toFinset.card) /
          prefixCount K n := by
    calc
      source n = (prefixCount A n : ℝ) / prefixCount E n := rfl
      _ ≤ (prefixCount A n : ℝ) / prefixCount K n := by
        exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hnR hdenom
      _ ≤ ((prefixCount (A ∩ K) n : ℝ) + hfinite.toFinset.card) /
          prefixCount K n := by
        exact div_le_div_of_nonneg_right hnumR hnR.le
  rw [show ((prefixCount (A ∩ K) n : ℝ) + hfinite.toFinset.card) /
      prefixCount K n = target n + error n by
        simp [target, error, add_div]] at hsource_le
  linarith

noncomputable def oracleOfFamily
    (family : LanguageFamily ℕ) (hinfinite : ∀ i, (family i).Infinite) :
    OracleFamily where
  language := family
  infinite' := hinfinite
  query i x := by
    classical
    exact if x ∈ family i then true else false
  query_spec i x := by
    classical
    simp

theorem stage3_countable_half_density : Stage3Case019.CountableClause := by
  intro q family hinfinite
  let O := oracleOfFamily family hinfinite
  let OE := finiteExpansionOracleFamily O
  refine ⟨semanticPatientGenerator OE, ?_⟩
  intro i input hinput
  obtain ⟨noise, hnoise, _hnoiseCard⟩ := hinput.2.2
  have hnoiseFinite : (Set.range input \ family i).Finite := by
    rw [← hnoise]
    exact noise.finite_toSet
  have hcontam :
      FiniteNoiseFiniteOmissionEnumeration input (O.language i) := by
    refine ⟨hinput.1, ?_, ?_⟩
    · exact
        (finiteNoise_iff_valuesOutside_finite_of_injective hinput.1).mpr
          hnoiseFinite
    · unfold FiniteOmissions
      have hempty : family i \ Set.range input = ∅ :=
        Set.diff_eq_empty.mpr hinput.2.1
      rw [show O.language i = family i by rfl, hempty]
      exact Set.finite_empty
  obtain ⟨j, _hjBase, hjPresents⟩ :=
    exists_finiteExpansion_index_for_stream O hcontam
  have hrun :=
    GenLimit.PatientMachine.patientScope_generation_and_lowerDensity
      OE input hjPresents
  have houtEq :
      Stage3Case019.outputAfterInput (semanticPatientGenerator OE) input =
        GenLimit.PatientMachine.output OE input := by
    funext t
    exact semanticPatientGenerator_outputAfterInput OE input t
  constructor
  · obtain ⟨Tpatient, hTpatient⟩ := hrun.1
    obtain ⟨Tseen, hTseen⟩ :=
      GenLimit.Generic.finset_eventually_subset_sample hjPresents
        hnoiseFinite.toFinset (by
          intro x hx
          rw [← hjPresents]
          exact (by simpa using hx : x ∈ Set.range input \ family i).1)
    refine ⟨max Tpatient Tseen, ?_⟩
    intro t ht
    have hp := hTpatient t ((Nat.le_max_left _ _).trans ht)
    have hs' : hnoiseFinite.toFinset ⊆ GenLimit.Generic.sample input (t + 1) := by
      intro x hx
      exact GenLimit.Generic.sample_mono
        (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_trans ht (Nat.le_succ t)))
        (hTseen hx)
    rw [houtEq]
    refine ⟨?_, ?_, hp.2.2⟩
    · by_contra hout
      have hbad : GenLimit.PatientMachine.output OE input t ∈
          hnoiseFinite.toFinset :=
        (by simpa using (show GenLimit.PatientMachine.output OE input t ∈
          Set.range input \ family i from ⟨hjPresents ▸ hp.1, hout⟩))
      have hsample := hs' hbad
      obtain ⟨s, hslt, hseq⟩ := GenLimit.Generic.mem_sample_iff.mp hsample
      exact hp.2.1 s (by omega) hseq
    · intro hsample
      obtain ⟨s, hslt, hseq⟩ := GenLimit.mem_sample_iff.mp hsample
      exact hp.2.1 s (by omega) hseq
  · let A := GenLimit.GeneratorFirst input
        (GenLimit.PatientMachine.output OE input) ∩ OE.language j
    have hA : A ⊆ OE.language j := Set.inter_subset_right
    have hKE : family i ⊆ OE.language j := by
      intro x hx
      rw [← hjPresents]
      exact hinput.2.1 hx
    have hfinite : (OE.language j \ family i).Finite := by
      rw [← hjPresents]
      exact hnoiseFinite
    have hdensity : (1 / 2 : ℝ) ≤ relativeLowerDensity A (OE.language j) := by
      exact hrun.2
    have htransfer := relativeLowerDensity_inter_of_finite_extension
      (hinfinite i) hKE hA hfinite hdensity
    have hset : A ∩ family i =
        GenLimit.GeneratorFirst input
          (GenLimit.PatientMachine.output OE input) ∩ family i := by
      ext x
      simp only [A, Set.mem_inter_iff]
      constructor
      · rintro ⟨⟨hxFirst, _hxE⟩, hxK⟩
        exact ⟨hxFirst, hxK⟩
      · rintro ⟨hxFirst, hxK⟩
        exact ⟨⟨hxFirst, hKE hxK⟩, hxK⟩
    rw [hset] at htransfer
    rw [houtEq]
    exact htransfer

end Stage3Case019Proof
