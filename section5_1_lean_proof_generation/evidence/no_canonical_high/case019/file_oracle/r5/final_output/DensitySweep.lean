import PairSweep

open Filter
open scoped Topology

namespace Stage3Case019.PairSweep

open GenLimit
open GenLimit.Generic
open GenLimit.NoiseLossFeedback
open GenLimit.UnionClosedness
open GenLimit.PatientScope

 theorem balanced_negative_even (p : ℕ) :
    balanced (4 * p + 1) = negativeCode (2 * p) := by
  simp [balanced, negativeCode]
  congr
  omega

 theorem balanced_negative_odd (p : ℕ) :
    balanced (4 * p + 3) = negativeCode (2 * p + 1) := by
  simp [balanced, negativeCode]
  congr
  omega

 theorem balanced_positive_even (p : ℕ) :
    balanced (4 * p + 2) = positiveCode (2 * p) := by
  simp [balanced, positiveCode]
  congr
  omega

 theorem balanced_positive_odd (p : ℕ) :
    balanced (4 * p + 4) = positiveCode (2 * p + 1) := by
  simp [balanced, positiveCode]
  congr
  omega

private theorem quarter_of_block_hits
    (D K : Set ℕ) (hDK : D ⊆ K) (B : ℕ)
    (hhit : ∀ p, B ≤ p →
      ∃ r, 4 * p < r ∧ r ≤ 4 * p + 4 ∧ r ∈ D) :
    (1 / 4 : ℝ) ≤ relativeLowerDensity D K := by
  classical
  let witness : ℕ → ℕ := fun p =>
    if hp : B ≤ p then Classical.choose (hhit p hp) else 0
  have hwitness {p : ℕ} (hp : B ≤ p) :
      4 * p < witness p ∧ witness p ≤ 4 * p + 4 ∧ witness p ∈ D := by
    simp only [witness, dif_pos hp]
    exact Classical.choose_spec (hhit p hp)
  have hinj : Set.InjOn witness {p : ℕ | B ≤ p} := by
    intro p hp r hr heq
    by_contra hne
    rcases lt_or_gt_of_ne hne with hpr | hrp
    · have hwp := hwitness hp
      have hwr := hwitness hr
      omega
    · have hwp := hwitness hp
      have hwr := hwitness hr
      omega
  have hcount : ∀ n, n ≤ 4 * prefixCount D n + (4 * B + 8) := by
    intro n
    by_cases hn : n = 0
    · simp [hn]
    let m := (n - 1) / 4
    by_cases hm : B ≤ m
    · have hsub : (Finset.Ico B m).image witness ⊆ prefixFinset D n := by
        intro r hr
        obtain ⟨p, hpIco, rfl⟩ := Finset.mem_image.mp hr
        have hpB : B ≤ p := (Finset.mem_Ico.mp hpIco).1
        have hpm : p < m := (Finset.mem_Ico.mp hpIco).2
        apply mem_prefixFinset.mpr
        refine ⟨?_, (hwitness hpB).2.2⟩
        have hnform : 4 * m ≤ n - 1 := Nat.mul_div_le (n - 1) 4
        have hnpos : 0 < n := Nat.pos_of_ne_zero hn
        calc
          witness p ≤ 4 * p + 4 := (hwitness hpB).2.1
          _ = 4 * (p + 1) := by omega
          _ ≤ 4 * m := Nat.mul_le_mul_left 4 (by omega)
          _ ≤ n - 1 := hnform
          _ < n := Nat.sub_lt hnpos (by omega)
      have hcardImage : ((Finset.Ico B m).image witness).card = m - B := by
        rw [Finset.card_image_iff.mpr]
        · simp
        · intro p hp r hr heq
          exact hinj (Finset.mem_Ico.mp hp).1 (Finset.mem_Ico.mp hr).1 heq
      have hlower : m - B ≤ prefixCount D n := by
        rw [← hcardImage]
        exact Finset.card_le_card hsub
      have hmform : 4 * m ≤ n - 1 := Nat.mul_div_le (n - 1) 4
      have hnupper : n - 1 < 4 * (m + 1) := by
        have := Nat.mod_lt (n - 1) (by omega : 0 < 4)
        have hdecomp := Nat.mod_add_div (n - 1) 4
        omega
      have hmdecomp : m = (m - B) + B := (Nat.sub_add_cancel hm).symm
      omega
    · have hmB : m < B := Nat.lt_of_not_ge hm
      have hnupper : n - 1 < 4 * (m + 1) := by
        have := Nat.mod_lt (n - 1) (by omega : 0 < 4)
        have hdecomp := Nat.mod_add_div (n - 1) 4
        omega
      omega
  let g : ℕ → ℝ := fun n =>
    (1 / 4 : ℝ) - ((4 * B + 8 : ℕ) : ℝ) / (4 * (n : ℝ))
  have hg : Tendsto g atTop (𝓝 (1 / 4 : ℝ)) := by
    have hz : Tendsto (fun n : ℕ => ((4 * B + 8 : ℕ) : ℝ) / (n : ℝ))
        atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    have hz4 := hz.div_const (4 : ℝ)
    simpa [g, div_div, mul_comm] using tendsto_const_nhds.sub hz4
  have hcompare : ∀ᶠ n : ℕ in atTop,
      g n ≤ (prefixCount D n : ℝ) / (prefixCount K n : ℝ) := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hboundR : (n : ℝ) ≤
        4 * (prefixCount D n : ℝ) + ((4 * B + 8 : ℕ) : ℝ) := by
      exact_mod_cast hcount n
    have hbase : g n ≤ (prefixCount D n : ℝ) / (n : ℝ) := by
      rw [show g n = (1 / 4 : ℝ) -
        ((4 * B + 8 : ℕ) : ℝ) / (4 * (n : ℝ)) by rfl]
      rw [le_div_iff₀ hnR]
      field_simp [hnR.ne']
      nlinarith
    by_cases hKzero : prefixCount K n = 0
    · have hDzero : prefixCount D n = 0 := by
        have := prefixCount_mono hDK n
        omega
      simp [hKzero, hDzero] at hbase ⊢
      exact hbase
    · have hKR : (0 : ℝ) < prefixCount K n := by
        exact_mod_cast Nat.pos_of_ne_zero hKzero
      have hKnNat : prefixCount K n ≤ n := by
        calc
          prefixCount K n ≤ prefixCount Set.univ n :=
            prefixCount_mono (Set.subset_univ K) n
          _ = n := by simp [prefixCount, prefixFinset]
      have hKn : (prefixCount K n : ℝ) ≤ n := by
        exact_mod_cast hKnNat
      exact hbase.trans (div_le_div_of_nonneg_left
        (Nat.cast_nonneg _) hKR hKn)
  have hlowerBound : IsBoundedUnder (· ≥ ·) atTop g := hg.isBoundedUnder_ge
  have hratioUpper : ∀ n, (prefixCount D n : ℝ) / (prefixCount K n : ℝ) ≤ 1 := by
    intro n
    by_cases hzero : prefixCount K n = 0
    · simp [hzero]
    · have hpos : (0 : ℝ) < prefixCount K n := by
        exact_mod_cast Nat.pos_of_ne_zero hzero
      rw [div_le_one hpos]
      exact_mod_cast prefixCount_mono hDK n
  calc
    (1 / 4 : ℝ) = liminf g atTop := hg.liminf_eq.symm
    _ ≤ liminf (fun n => (prefixCount D n : ℝ) / (prefixCount K n : ℝ)) atTop :=
      liminf_le_liminf hcompare hlowerBound
        (isCoboundedUnder_ge_of_le atTop hratioUpper)
    _ = relativeLowerDensity D K := rfl

 theorem first_density
    {q : ℕ} {K : Set ℤ} (hK : K ∈ finiteOmissionFirstClass q)
    {input : Stream ℤ}
    (henum : InjectiveValueContaminatedPresentationAtMost input K q) :
    (1 / 4 : ℝ) ≤ balancedRelativeLowerDensity
      (GeneratorFirstOn input (outputAfterInput (generator q) input) ∩ K) K := by
  let A := GeneratorFirstOn input (outputAfterInput (generator q) input) ∩ K
  let D := balancedRanks A
  let KR := balancedRanks K
  have hDK : D ⊆ KR := by
    intro r hr
    exact hr.2
  obtain ⟨B, hB⟩ := first_pair_secured hK henum
  apply quarter_of_block_hits D KR hDK B
  intro p hp
  obtain ⟨z, hzpair, hzK, hzfirst⟩ := hB p hp
  rcases hzpair with hz | hz
  · refine ⟨4 * p + 2, by omega, by omega, ?_⟩
    change balanced (4 * p + 2) ∈ A
    rw [balanced_positive_even]
    have hz' : z = positiveCode (2 * p) := by simpa [code] using hz
    rw [← hz']
    exact ⟨hzfirst, hzK⟩
  · refine ⟨4 * p + 4, by omega, by omega, ?_⟩
    change balanced (4 * p + 4) ∈ A
    rw [balanced_positive_odd]
    have hz' : z = positiveCode (2 * p + 1) := by simpa [code] using hz
    rw [← hz']
    exact ⟨hzfirst, hzK⟩

 theorem second_density
    {q : ℕ} {K : Set ℤ} (hK : K ∈ finiteOmissionSecondClass q)
    {input : Stream ℤ}
    (henum : InjectiveValueContaminatedPresentationAtMost input K q) :
    (1 / 4 : ℝ) ≤ balancedRelativeLowerDensity
      (GeneratorFirstOn input (outputAfterInput (generator q) input) ∩ K) K := by
  let A := GeneratorFirstOn input (outputAfterInput (generator q) input) ∩ K
  let D := balancedRanks A
  let KR := balancedRanks K
  have hDK : D ⊆ KR := by
    intro r hr
    exact hr.2
  apply quarter_of_block_hits D KR hDK 0
  intro p _
  obtain ⟨z, hzpair, hzK, hzfirst⟩ := second_pair_secured hK henum p
  rcases hzpair with hz | hz
  · refine ⟨4 * p + 1, by omega, by omega, ?_⟩
    change balanced (4 * p + 1) ∈ A
    rw [balanced_negative_even]
    have hz' : z = negativeCode (2 * p) := by simpa [code] using hz
    rw [← hz']
    exact ⟨hzfirst, hzK⟩
  · refine ⟨4 * p + 3, by omega, by omega, ?_⟩
    change balanced (4 * p + 3) ∈ A
    rw [balanced_negative_odd]
    have hz' : z = negativeCode (2 * p + 1) := by simpa [code] using hz
    rw [← hz']
    exact ⟨hzfirst, hzK⟩

end Stage3Case019.PairSweep
