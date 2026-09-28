import output.SeparationMain

open Filter
open scoped Topology
open Stage3Case019

namespace Case019

noncomputable def denseSweepRank (q : ℕ) (input : Stage3Case019.Stream ℤ) (t : ℕ) : ℕ :=
  Classical.choose (denseSweep_output_rank_bound q t input)

lemma denseSweepRank_le (q : ℕ) (input : Stage3Case019.Stream ℤ) (t : ℕ) :
    denseSweepRank q input t ≤ 4 * (t + 1) :=
  (Classical.choose_spec (denseSweep_output_rank_bound q t input)).1

lemma balanced_denseSweepRank (q : ℕ) (input : Stage3Case019.Stream ℤ) (t : ℕ) :
    balanced (denseSweepRank q input t) =
      outputAfterInput (denseSweepGenerator q) input t :=
  (Classical.choose_spec (denseSweep_output_rank_bound q t input)).2

lemma denseSweep_prefixCount_lower
    (q : ℕ) (input : Stage3Case019.Stream ℤ) (K : Stage3Case019.Language ℤ)
    {T : ℕ}
    (hvalid : ∀ t, T ≤ t →
      outputAfterInput (denseSweepGenerator q) input t ∈ K ∧
      outputAfterInput (denseSweepGenerator q) input t ∉
        GenLimit.Generic.sample input (t + 1) ∧
      ∀ s, s < t →
        outputAfterInput (denseSweepGenerator q) input s ≠
          outputAfterInput (denseSweepGenerator q) input t) :
    ∀ n,
      n / 4 - (T + 1) ≤
        GenLimit.PatientScope.prefixCount
          (balancedRanks
            (GeneratorFirstOn input
              (outputAfterInput (denseSweepGenerator q) input) ∩ K)) n := by
  classical
  intro n
  let times : Finset ℕ := Finset.Ico T (n / 4 - 1)
  let ranks : Finset ℕ := times.image (denseSweepRank q input)
  let D := balancedRanks
    (GeneratorFirstOn input
      (outputAfterInput (denseSweepGenerator q) input) ∩ K)
  have hrank_inj : Set.InjOn (denseSweepRank q input) (↑times : Set ℕ) := by
    intro s hs t ht heq
    by_contra hne
    rcases lt_or_gt_of_ne hne with hst | hts
    · have hsT : T ≤ s := (Finset.mem_Ico.mp hs).1
      have htT : T ≤ t := (Finset.mem_Ico.mp ht).1
      have houtne := (hvalid t htT).2.2 s hst
      apply houtne
      rw [← balanced_denseSweepRank q input s,
        ← balanced_denseSweepRank q input t, heq]
    · have hsT : T ≤ s := (Finset.mem_Ico.mp hs).1
      have htT : T ≤ t := (Finset.mem_Ico.mp ht).1
      have houtne := (hvalid s hsT).2.2 t hts
      apply houtne
      rw [← balanced_denseSweepRank q input t,
        ← balanced_denseSweepRank q input s, heq]
  have hranks_sub : ranks ⊆ GenLimit.PatientScope.prefixFinset D n := by
    intro r hr
    rw [Finset.mem_image] at hr
    obtain ⟨t, ht, rfl⟩ := hr
    have htIco := Finset.mem_Ico.mp ht
    have htT : T ≤ t := htIco.1
    have htupper : t < n / 4 - 1 := htIco.2
    apply GenLimit.PatientScope.mem_prefixFinset.mpr
    constructor
    · have hrle := denseSweepRank_le q input t
      omega
    · change balanced (denseSweepRank q input t) ∈
        GeneratorFirstOn input
          (outputAfterInput (denseSweepGenerator q) input) ∩ K
      rw [balanced_denseSweepRank]
      constructor
      · refine ⟨t, rfl, ?_⟩
        intro s hst heq
        have hmem : outputAfterInput (denseSweepGenerator q) input t ∈
            GenLimit.Generic.sample input (t + 1) := by
          apply GenLimit.Generic.mem_sample_iff.mpr
          exact ⟨s, by omega, heq⟩
        exact (hvalid t htT).2.1 hmem
      · exact (hvalid t htT).1
  have hcardRanks : ranks.card = times.card := by
    dsimp [ranks]
    rw [Finset.card_image_iff.mpr]
    intro a ha b hb hab
    exact hrank_inj ha hb hab
  calc
    n / 4 - (T + 1) = times.card := by
      simp [times]
      omega
    _ = ranks.card := hcardRanks.symm
    _ ≤ (GenLimit.PatientScope.prefixFinset D n).card :=
      Finset.card_le_card hranks_sub
    _ = GenLimit.PatientScope.prefixCount D n := rfl

end Case019

namespace Case019

lemma denseSweep_quarter_density
    (q : ℕ) (input : Stage3Case019.Stream ℤ) (K : Stage3Case019.Language ℤ)
    (hnovel : NovelGeneratesAfterInput input
      (outputAfterInput (denseSweepGenerator q) input) K) :
    (1 / 4 : ℝ) ≤ balancedRelativeLowerDensity
      (GeneratorFirstOn input
        (outputAfterInput (denseSweepGenerator q) input) ∩ K) K := by
  classical
  obtain ⟨T, hvalid⟩ := hnovel
  let D := balancedRanks
    (GeneratorFirstOn input
      (outputAfterInput (denseSweepGenerator q) input) ∩ K)
  let B := balancedRanks K
  let C := T + 1
  let g : ℕ → ℝ := fun n => (1 / 4 : ℝ) - (C + 1 : ℕ) / (n : ℝ)
  have hDsubB : D ⊆ B := by
    intro r hr
    exact hr.2
  have hg : Tendsto g atTop (𝓝 (1 / 4 : ℝ)) := by
    have hzero := tendsto_const_div_atTop_nhds_zero_nat ((C + 1 : ℕ) : ℝ)
    simpa [g] using hzero.const_sub (1 / 4 : ℝ)
  have hcompare : ∀ᶠ n : ℕ in atTop,
      g n ≤
        (GenLimit.PatientScope.prefixCount D n : ℝ) /
          (GenLimit.PatientScope.prefixCount B n : ℝ) := by
    filter_upwards [eventually_ge_atTop (4 * (C + 1))] with n hn
    let m := n / 4
    have hmC : C ≤ m := by dsimp [m]; omega
    have hmC1 : C + 1 ≤ m := by dsimp [m]; omega
    have hcountNat : m - C ≤ GenLimit.PatientScope.prefixCount D n := by
      dsimp [m, C, D]
      exact denseSweep_prefixCount_lower q input K hvalid n
    have hcountR : ((m - C : ℕ) : ℝ) ≤
        GenLimit.PatientScope.prefixCount D n := by exact_mod_cast hcountNat
    have hfloorNat : n < 4 * (m + 1) := by dsimp [m]; omega
    have hfloorR : (n : ℝ) < 4 * ((m : ℝ) + 1) := by exact_mod_cast hfloorNat
    have hnposNat : 0 < n := by omega
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hnposNat
    have hbase : g n ≤ ((m - C : ℕ) : ℝ) / (n : ℝ) := by
      rw [show ((m - C : ℕ) : ℝ) = (m : ℝ) - C by
        rw [Nat.cast_sub hmC]]
      rw [le_div_iff₀ hnpos]
      dsimp [g]
      field_simp [hnpos.ne']
      push_cast at *
      nlinarith [hfloorR]
    have htoD : ((m - C : ℕ) : ℝ) / (n : ℝ) ≤
        (GenLimit.PatientScope.prefixCount D n : ℝ) / (n : ℝ) := by
      exact div_le_div_of_nonneg_right hcountR hnpos.le
    have hB_le_n : GenLimit.PatientScope.prefixCount B n ≤ n := by
      unfold GenLimit.PatientScope.prefixCount GenLimit.PatientScope.prefixFinset
      exact (Finset.card_filter_le _ _).trans_eq (Finset.card_range n)
    have hDposNat : 0 < GenLimit.PatientScope.prefixCount D n := by
      have : 0 < m - C := by omega
      omega
    have hBposNat : 0 < GenLimit.PatientScope.prefixCount B n := by
      have hDB := GenLimit.PatientScope.prefixCount_mono hDsubB n
      omega
    have hBpos : (0 : ℝ) < GenLimit.PatientScope.prefixCount B n := by
      exact_mod_cast hBposNat
    have hDtoB :
        (GenLimit.PatientScope.prefixCount D n : ℝ) / (n : ℝ) ≤
          (GenLimit.PatientScope.prefixCount D n : ℝ) /
            (GenLimit.PatientScope.prefixCount B n : ℝ) := by
      apply div_le_div_of_nonneg_left
      · positivity
      · exact hBpos
      · exact_mod_cast hB_le_n
    exact hbase.trans (htoD.trans hDtoB)
  have hratio_le_one : ∀ n,
      (GenLimit.PatientScope.prefixCount D n : ℝ) /
          (GenLimit.PatientScope.prefixCount B n : ℝ) ≤ 1 := by
    intro n
    by_cases hzero : GenLimit.PatientScope.prefixCount B n = 0
    · simp [hzero]
    · have hpos : (0 : ℝ) < GenLimit.PatientScope.prefixCount B n := by
        exact_mod_cast Nat.pos_of_ne_zero hzero
      rw [div_le_one hpos]
      exact_mod_cast GenLimit.PatientScope.prefixCount_mono hDsubB n
  change (1 / 4 : ℝ) ≤ liminf
    (fun n : ℕ => (GenLimit.PatientScope.prefixCount D n : ℝ) /
      (GenLimit.PatientScope.prefixCount B n : ℝ)) atTop
  calc
    (1 / 4 : ℝ) = liminf g atTop := hg.liminf_eq.symm
    _ ≤ _ := liminf_le_liminf hcompare hg.isBoundedUnder_ge
      (isCoboundedUnder_ge_of_le atTop hratio_le_one)

end Case019
