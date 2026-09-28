import Helpers

open Set Filter
open scoped Topology

namespace Case019Helpers

open GenLimit
open GenLimit.Generic
open GenLimit.PatientMachine
open GenLimit.InfiniteContamination

noncomputable def ambientRatio (A K : Set ℕ) (n : ℕ) : ℝ :=
  (PatientScope.prefixCount A n : ℝ) / (PatientScope.prefixCount K n : ℝ)

theorem ambientRatio_nonneg (A K : Set ℕ) (n : ℕ) :
    0 ≤ ambientRatio A K n := by
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem ambientRatio_le_one {A K : Set ℕ} (hAK : A ⊆ K) (n : ℕ) :
    ambientRatio A K n ≤ 1 := by
  by_cases hzero : PatientScope.prefixCount K n = 0
  · simp [ambientRatio, hzero]
  · rw [ambientRatio, div_le_one]
    · exact_mod_cast PatientScope.prefixCount_mono hAK n
    · exact_mod_cast Nat.pos_of_ne_zero hzero

theorem relativeLowerDensity_transfer_subset_finite
    {D K E : Set ℕ} (hKE : K ⊆ E) (hfinite : (E \ K).Finite)
    (hE : E.Infinite) :
    PatientScope.relativeLowerDensity (D ∩ E) E ≤
      PatientScope.relativeLowerDensity (D ∩ K) K := by
  let f : ℕ → ℝ := ambientRatio (D ∩ E) E
  let g : ℕ → ℝ := ambientRatio (D ∩ K) K
  have hdiff : ((D ∩ E) \ (D ∩ K)).Finite := by
    apply hfinite.subset
    intro x hx
    exact ⟨hx.1.2, fun hxK => hx.2 ⟨hx.1.1, hxK⟩⟩
  let c : ℝ := hdiff.toFinset.card
  have hcount : ∀ n,
      PatientScope.prefixCount (D ∩ E) n ≤
        PatientScope.prefixCount (D ∩ K) n + hdiff.toFinset.card := by
    intro n
    classical
    let A := ((Finset.range n).filter fun x => x ∈ D ∩ E)
    let B := ((Finset.range n).filter fun x => x ∈ D ∩ K)
    let F := hdiff.toFinset
    have hsub : A ⊆ B ∪ F := by
      intro x hx
      simp only [A, B, Finset.mem_filter, Finset.mem_union] at hx ⊢
      by_cases hxK : x ∈ K
      · exact Or.inl ⟨hx.1, hx.2.1, hxK⟩
      · exact Or.inr (Set.Finite.mem_toFinset hdiff |>.2 ⟨hx.2, fun h => hxK h.2⟩)
    have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le B F)
    simpa [PatientScope.prefixCount, PatientScope.prefixFinset, A, B, F] using hc
  have hratio : ∀ n,
      f n ≤ g n + c / (PatientScope.prefixCount E n : ℝ) := by
    intro n
    dsimp [f, g, ambientRatio]
    by_cases hKzero : PatientScope.prefixCount K n = 0
    · have hAKzero : PatientScope.prefixCount (D ∩ K) n = 0 := by
        exact Nat.eq_zero_of_le_zero
          ((PatientScope.prefixCount_mono inter_subset_right n).trans_eq hKzero)
      by_cases hEzero : PatientScope.prefixCount E n = 0
      · simp [f, g, ambientRatio, hKzero, hEzero]
      · have hEposR : (0 : ℝ) < PatientScope.prefixCount E n := by
          exact_mod_cast Nat.pos_of_ne_zero hEzero
        have hnumNat : PatientScope.prefixCount (D ∩ E) n ≤ hdiff.toFinset.card := by
          simpa [hAKzero] using hcount n
        have hnum : (PatientScope.prefixCount (D ∩ E) n : ℝ) ≤ c := by
          change (PatientScope.prefixCount (D ∩ E) n : ℝ) ≤
            (hdiff.toFinset.card : ℝ)
          exact_mod_cast hnumNat
        simp only [hKzero, hAKzero, Nat.cast_zero, zero_div, zero_add]
        exact div_le_div_of_nonneg_right hnum (le_of_lt hEposR)
    · have hKposR : (0 : ℝ) < PatientScope.prefixCount K n := by
        exact_mod_cast Nat.pos_of_ne_zero hKzero
      have hEposR : (0 : ℝ) < PatientScope.prefixCount E n := by
        have hle := PatientScope.prefixCount_mono hKE n
        exact_mod_cast lt_of_lt_of_le (Nat.pos_of_ne_zero hKzero) hle
      have hnum : (PatientScope.prefixCount (D ∩ E) n : ℝ) ≤
          PatientScope.prefixCount (D ∩ K) n + hdiff.toFinset.card := by
        exact_mod_cast hcount n
      have hden : (PatientScope.prefixCount K n : ℝ) ≤
          PatientScope.prefixCount E n := by
        exact_mod_cast PatientScope.prefixCount_mono hKE n
      calc
        (PatientScope.prefixCount (D ∩ E) n : ℝ) /
              (PatientScope.prefixCount E n : ℝ) ≤ ((PatientScope.prefixCount (D ∩ K) n : ℝ) + c) /
            (PatientScope.prefixCount E n : ℝ) := by
          exact div_le_div_of_nonneg_right hnum (le_of_lt hEposR)
        _ = (PatientScope.prefixCount (D ∩ K) n : ℝ) /
              (PatientScope.prefixCount E n : ℝ) +
            c / (PatientScope.prefixCount E n : ℝ) := by ring
        _ ≤ g n + c / (PatientScope.prefixCount E n : ℝ) := by
          gcongr
          exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hKposR hden
  have herr : Tendsto
      (fun n => c / (PatientScope.prefixCount E n : ℝ)) atTop (𝓝 0) := by
    have hden : Tendsto
        (fun n => (PatientScope.prefixCount E n : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp
        (PatientScope.tendsto_prefixCount_atTop hE)
    exact tendsto_const_nhds.div_atTop hden
  have hfLower : IsBoundedUnder (fun x y : ℝ => x ≥ y) atTop f :=
    isBoundedUnder_of ⟨0, fun n => ambientRatio_nonneg _ _ n⟩
  have hgLower : IsBoundedUnder (fun x y : ℝ => x ≥ y) atTop g :=
    isBoundedUnder_of ⟨0, fun n => ambientRatio_nonneg _ _ n⟩
  have hgCob : IsCoboundedUnder (fun x y : ℝ => x ≥ y) atTop g :=
    isCoboundedUnder_ge_of_le atTop (fun n => ambientRatio_le_one
      inter_subset_right n)
  rw [PatientScope.relativeLowerDensity, PatientScope.relativeLowerDensity]
  change liminf f atTop ≤ liminf g atTop
  apply le_of_forall_pos_le_add
  intro ε hε
  have hevent : ∀ᶠ n in atTop, f n ≤ g n + ε := by
    filter_upwards [herr.eventually (eventually_le_nhds hε)] with n hn
    exact (hratio n).trans (add_le_add_left hn _)
  calc
    liminf f atTop ≤ liminf (fun n => g n + ε) atTop :=
      liminf_le_liminf hevent hfLower
        (isCoboundedUnder_ge_of_le atTop fun n => by
          dsimp [g]
          exact add_le_add_right (ambientRatio_le_one inter_subset_right n) ε)
    _ = liminf g atTop + ε :=
      liminf_add_const atTop g ε hgCob hgLower

 theorem countable_half_density : Stage3Case019.CountableClause := by
  intro q family hinf
  let O := oracleOfFamily family hinf
  let E := finiteExpansionOracleFamily O
  refine ⟨patientGenerator E, ?_⟩
  intro i input hinput
  have hcontam : FiniteNoiseFiniteOmissionEnumeration input (O.language i) := by
    refine ⟨hinput.1, ?_, ?_⟩
    · exact (finite_valuesOutside_iff_finitelyManyViolations_of_injective hinput.1).mp
        ((setDifferenceAtMost_iff_finite_ncard_le _ _ q).mp hinput.2.2).1
    · simp only [FiniteOmissions]
      change (family i \ Set.range input).Finite
      rw [Set.diff_eq_empty.mpr hinput.2.1]
      exact Set.finite_empty
  obtain ⟨j, _hjbase, hjpresent⟩ :=
    exists_finiteExpansion_index_for_stream O hcontam
  obtain ⟨hvalid, hdensity⟩ :=
    patientScope_generation_and_lowerDensity E input hjpresent
  have hout := outputAfterInput_patientGenerator E input
  constructor
  · rcases hvalid with ⟨T, hT⟩
    have hbadFinite : (E.language j \ family i).Finite := by
      rw [← hjpresent]
      exact ((setDifferenceAtMost_iff_finite_ncard_le _ _ q).mp hinput.2.2).1
    have houtinj : Function.Injective (PatientMachine.output E input) := by
      intro s t hst
      rcases lt_trichotomy s t with h | h | h
      · exact False.elim ((output_ne_of_lt E input h) hst)
      · exact h
      · exact False.elim ((output_ne_of_lt E input h) hst.symm)
    have hpreFinite :
        ((PatientMachine.output E input) ⁻¹' (E.language j \ family i)).Finite :=
      hbadFinite.preimage houtinj.injOn
    obtain ⟨Tb, hTb⟩ := hpreFinite.bddAbove
    refine ⟨max T (Tb + 1), ?_⟩
    intro t ht
    have htT : T ≤ t := le_trans (Nat.le_max_left _ _) ht
    have htBad : Tb < t := by omega
    have hv := hT t htT
    refine ⟨?_, ?_, ?_⟩
    · rw [hout]
      by_contra hnot
      have hmem : t ∈ (PatientMachine.output E input) ⁻¹' (E.language j \ family i) :=
        ⟨hv.1, hnot⟩
      exact (not_le_of_gt htBad) (hTb hmem)
    · rw [hout]
      intro hsample
      rw [GenLimit.mem_sample_iff] at hsample
      obtain ⟨s, hs, heq⟩ := hsample
      exact hv.2.1 s (by omega) heq
    · intro s hs
      rw [hout s, hout t]
      exact hv.2.2 s hs
  · have houtfun :
        Stage3Case019.outputAfterInput (patientGenerator E) input =
          PatientMachine.output E input := funext hout
    rw [houtfun]
    have hKE : family i ⊆ E.language j := by
      rw [← hjpresent]
      exact hinput.2.1
    have hfinite : (E.language j \ family i).Finite := by
      rw [← hjpresent]
      exact ((setDifferenceAtMost_iff_finite_ncard_le _ _ q).mp hinput.2.2).1
    exact hdensity.trans
      (relativeLowerDensity_transfer_subset_finite hKE hfinite (E.infinite' j))

end Case019Helpers
