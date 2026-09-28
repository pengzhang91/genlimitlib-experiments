import Partial
import Mathlib

open Set Filter
open scoped Topology
open Stage3Case019

namespace Case019

@[simp] theorem balanced_two_posLine (n : ℕ) :
    balanced (2 * n) = posLine n := by
  cases n with
  | zero => rfl
  | succ n =>
      rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega]
      rw [balanced, if_neg (by omega)]
      change Int.ofNat ((2 * n + 1) / 2 + 1) = Int.ofNat (n + 1)
      congr 1
      omega

 theorem greedy_output_generatorFirst
    (input : Stream ℤ) (t : ℕ) :
    outputAfterInput (greedyGenerator posLine posLine_injective) input t ∈
      GeneratorFirstOn input
        (outputAfterInput (greedyGenerator posLine posLine_injective) input) := by
  refine ⟨t, rfl, ?_⟩
  intro s hst heq
  have hnot := greedy_output_not_sample posLine posLine_injective input t
  apply hnot
  simp only [GenLimit.Generic.sample, Finset.mem_image]
  exact ⟨s, Finset.mem_range.mpr (by omega), heq⟩

 theorem greedy_output_mem_commonHalf
    {K : Stage3Case019.Language ℤ} (hK : K ∈ commonHalfFamily)
    (input : Stream ℤ) (t : ℕ) :
    outputAfterInput (greedyGenerator posLine posLine_injective) input t ∈ K := by
  apply hK
  exact greedy_output_mem_line posLine posLine_injective input t

 theorem prefix_output_count_lower
    {K : Stage3Case019.Language ℤ} (hK : K ∈ commonHalfFamily)
    (input : Stream ℤ) (m : ℕ) :
    m / 4 ≤ GenLimit.PatientScope.prefixCount
      (balancedRanks
        (GeneratorFirstOn input
          (outputAfterInput (greedyGenerator posLine posLine_injective) input) ∩ K)) m := by
  classical
  let r := m / 4
  let output := outputAfterInput (greedyGenerator posLine posLine_injective) input
  let D := GeneratorFirstOn input output ∩ K
  let ranks : Fin r → ℕ := fun s =>
    2 * Classical.choose (greedy_output_rank_bound posLine posLine_injective input s)
  have hrank_lt (s : Fin r) : ranks s < m := by
    have hspec := Classical.choose_spec
      (greedy_output_rank_bound posLine posLine_injective input s)
    rcases hspec with ⟨hchosen, _⟩
    simp only [ranks]
    have hs : s.val < m / 4 := s.isLt
    omega
  have hrank_mem (s : Fin r) : ranks s ∈ balancedRanks D := by
    obtain ⟨n, hn, hout⟩ := greedy_output_rank_bound posLine posLine_injective input s
    have hspec := Classical.choose_spec
      (greedy_output_rank_bound posLine posLine_injective input s)
    rcases hspec with ⟨_, houtchosen⟩
    change balanced (ranks s) ∈ D
    simp only [ranks, balanced_two_posLine]
    rw [← houtchosen]
    exact ⟨greedy_output_generatorFirst input s,
      greedy_output_mem_commonHalf hK input s⟩
  have hranks_inj : Function.Injective ranks := by
    intro a b hab
    have houtinj := greedy_output_injective posLine posLine_injective input
    apply Fin.ext
    apply houtinj
    have ha := Classical.choose_spec
      (greedy_output_rank_bound posLine posLine_injective input a)
    have hb := Classical.choose_spec
      (greedy_output_rank_bound posLine posLine_injective input b)
    rcases ha with ⟨_, haout⟩
    rcases hb with ⟨_, hbout⟩
    have hchoose : Classical.choose
        (greedy_output_rank_bound posLine posLine_injective input a) =
        Classical.choose
          (greedy_output_rank_bound posLine posLine_injective input b) := by
      simp only [ranks] at hab
      omega
    rw [haout, hbout, hchoose]
  let imageRanks : Finset ℕ := Finset.univ.image ranks
  have hsub : imageRanks ⊆ GenLimit.PatientScope.prefixFinset (balancedRanks D) m := by
    intro n hn
    rcases Finset.mem_image.mp hn with ⟨s, _, rfl⟩
    simp only [GenLimit.PatientScope.prefixFinset, Finset.mem_filter,
      Finset.mem_range]
    exact ⟨hrank_lt s, hrank_mem s⟩
  calc
    m / 4 = imageRanks.card := by
      rw [Finset.card_image_of_injective _ hranks_inj, Finset.card_univ, Fintype.card_fin]
    _ ≤ (GenLimit.PatientScope.prefixFinset (balancedRanks D) m).card :=
      Finset.card_le_card hsub
    _ = GenLimit.PatientScope.prefixCount (balancedRanks D) m := rfl

 theorem prefixCount_le_index (S : Set ℕ) (m : ℕ) :
    GenLimit.PatientScope.prefixCount S m ≤ m := by
  classical
  unfold GenLimit.PatientScope.prefixCount GenLimit.PatientScope.prefixFinset
  exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (Finset.card_range m)

 theorem commonHalf_quarter_density
    {K : Stage3Case019.Language ℤ} (hK : K ∈ commonHalfFamily)
    (input : Stream ℤ) :
    (1 / 4 : ℝ) ≤ balancedRelativeLowerDensity
      (GeneratorFirstOn input
        (outputAfterInput (greedyGenerator posLine posLine_injective) input) ∩ K) K := by
  let D := GeneratorFirstOn input
    (outputAfterInput (greedyGenerator posLine posLine_injective) input) ∩ K
  let numer : ℕ → ℕ := fun m => GenLimit.PatientScope.prefixCount (balancedRanks D) m
  let denom : ℕ → ℕ := fun m => GenLimit.PatientScope.prefixCount (balancedRanks K) m
  have hdenom_pos : ∀ᶠ m in atTop, 0 < denom m := by
    filter_upwards [eventually_ge_atTop 1] with m hm
    have hzero : (0 : ℤ) ∈ K := hK ⟨0, rfl⟩
    have : 0 ∈ GenLimit.PatientScope.prefixFinset (balancedRanks K) m := by
      simp only [GenLimit.PatientScope.prefixFinset, Finset.mem_filter,
        Finset.mem_range, balancedRanks, Set.mem_preimage]
      exact ⟨hm, hzero⟩
    have := Finset.card_pos.mpr ⟨0, this⟩
    exact this
  have hlower : ∀ᶠ (m : ℕ) in atTop,
      (1 / 4 : ℝ) - 1 / (m : ℝ) ≤ (numer m : ℝ) / (denom m : ℝ) := by
    filter_upwards [eventually_ge_atTop 1, hdenom_pos] with m hm hdp
    have hn : m / 4 ≤ numer m := by
      simpa [numer, D] using prefix_output_count_lower hK input m
    have hd := prefixCount_le_index (balancedRanks K) m
    have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
    have hdenpos : (0 : ℝ) < denom m := by exact_mod_cast hdp
    have hnreal : ((m / 4 : ℕ) : ℝ) ≤ numer m := by exact_mod_cast hn
    have hm_lt : m < 4 * (m / 4 + 1) := by omega
    have hm_lt_real : (m : ℝ) < 4 * ((m / 4 + 1 : ℕ) : ℝ) := by
      exact_mod_cast hm_lt
    have hfloor : (m : ℝ) / 4 - 1 ≤ ((m / 4 : ℕ) : ℝ) := by
      norm_num at hm_lt_real ⊢
      linarith
    have hnum : (m : ℝ) / 4 - 1 ≤ numer m := hfloor.trans hnreal
    have hratio : ((m : ℝ) / 4 - 1) / m ≤ (numer m : ℝ) / (denom m : ℝ) := by
      apply div_le_div₀
      · have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
        linarith
      · exact hnum
      · exact hdenpos
      · exact_mod_cast hd
    convert hratio using 1 <;> field_simp <;> ring
  unfold balancedRelativeLowerDensity GenLimit.PatientScope.relativeLowerDensity
  change (1 / 4 : ℝ) ≤ liminf (fun m => (numer m : ℝ) / (denom m : ℝ)) atTop
  have htend : Tendsto (fun m : ℕ => (1 / 4 : ℝ) - 1 / (m : ℝ)) atTop (𝓝 (1 / 4)) := by
    simpa using (tendsto_const_nhds.sub tendsto_one_div_atTop_nhds_zero_nat)
  rw [← htend.liminf_eq]
  have hlower_bdd : IsBoundedUnder (fun x y : ℝ => x ≥ y) atTop
      (fun m : ℕ => (1 / 4 : ℝ) - 1 / (m : ℝ)) := by
    apply isBoundedUnder_of_eventually_ge (a := 0)
    filter_upwards [eventually_ge_atTop 4] with m hm
    have hmreal : (4 : ℝ) ≤ m := by exact_mod_cast hm
    have hinv : 1 / (m : ℝ) ≤ (1 / 4 : ℝ) :=
      one_div_le_one_div_of_le (by norm_num) hmreal
    linarith
  have hratio_upper : ∀ᶠ (m : ℕ) in atTop,
      (numer m : ℝ) / (denom m : ℝ) ≤ 1 := by
    filter_upwards [hdenom_pos] with m hdp
    have hsubset : balancedRanks D ⊆ balancedRanks K := by
      intro n hn
      exact hn.2
    have hcount : numer m ≤ denom m := by
      dsimp [numer, denom]
      unfold GenLimit.PatientScope.prefixCount GenLimit.PatientScope.prefixFinset
      apply Finset.card_le_card
      intro n hn
      simp only [Finset.mem_filter, Finset.mem_range] at hn ⊢
      exact ⟨hn.1, hsubset hn.2⟩
    have hdenreal : (0 : ℝ) < denom m := by exact_mod_cast hdp
    rw [div_le_one hdenreal]
    exact_mod_cast hcount
  exact liminf_le_liminf hlower (hu := hlower_bdd)
    (hv := isCoboundedUnder_ge_of_eventually_le atTop hratio_upper)

 theorem commonHalfFamily_uniform_quarter :
    ∃ gen : Generator ℤ,
      ∀ K ∈ commonHalfFamily, ∀ input : Stream ℤ,
        NovelGeneratesAfterInput input (outputAfterInput gen input) K ∧
        (1 / 4 : ℝ) ≤ balancedRelativeLowerDensity
          (GeneratorFirstOn input (outputAfterInput gen input) ∩ K) K := by
  refine ⟨greedyGenerator posLine posLine_injective, ?_⟩
  intro K hK input
  exact ⟨greedy_novel_after_input posLine posLine_injective input K hK,
    commonHalf_quarter_density hK input⟩

end Case019
