import Diagonal
import GenLimit.Paper39_DenseGeneration.Abstract.Density

namespace Stage3Work

open Stage3S2B
open Filter

private theorem core_prefixCount_le_log (gen : FeedbackGenerator) (n : ℕ) :
    (diagonalOrdered gen).prefixCount core n ≤ Nat.log 2 (3 * n) + 1 := by
  classical
  let S := (Finset.range n).filter fun i =>
    (diagonalTranscript gen).presentation i ∈ core
  let exponents := S.image fun i =>
    Nat.log 2 ((diagonalTranscript gen).presentation i)
  have hinj : Set.InjOn
      (fun i => Nat.log 2 ((diagonalTranscript gen).presentation i)) S := by
    intro i hi j hj hij
    have hiCore : (diagonalTranscript gen).presentation i ∈ core := by
      exact (Finset.mem_filter.mp hi).2
    have hjCore : (diagonalTranscript gen).presentation j ∈ core := by
      exact (Finset.mem_filter.mp hj).2
    rcases hiCore with ⟨ki, hki⟩
    rcases hjCore with ⟨kj, hkj⟩
    have hk : ki = kj := by
      dsimp at hij
      rw [← hki, ← hkj] at hij
      simpa using hij
    apply diagonal_presentation_injective gen
    calc
      (diagonalTranscript gen).presentation i = 2 ^ ki := hki.symm
      _ = 2 ^ kj := congrArg (fun k : ℕ => 2 ^ k) hk
      _ = (diagonalTranscript gen).presentation j := hkj
  have hcard : S.card = exponents.card := by
    symm
    exact Finset.card_image_iff.mpr hinj
  have hsubset : exponents ⊆ Finset.range (Nat.log 2 (3 * n) + 1) := by
    intro k hk
    rcases Finset.mem_image.mp hk with ⟨i, hi, rfl⟩
    have hin : i < n := by
      exact Finset.mem_range.mp (Finset.mem_filter.mp hi).1
    apply Finset.mem_range.mpr
    apply Nat.lt_succ_of_le
    apply Nat.log_mono_right
    calc
      (diagonalTranscript gen).presentation i ≤ 3 * i :=
        diagonal_presentation_le gen i
      _ ≤ 3 * n := by omega
  change S.card ≤ Nat.log 2 (3 * n) + 1
  rw [hcard]
  calc
    exponents.card ≤ (Finset.range (Nat.log 2 (3 * n) + 1)).card :=
      Finset.card_le_card hsubset
    _ = Nat.log 2 (3 * n) + 1 := Finset.card_range _

private theorem log_three_mul_le (n : ℕ) :
    Nat.log 2 (3 * n) + 1 ≤ 3 + Nat.log2 n := by
  rw [Nat.log2_eq_log_two]
  by_cases hn : n = 0
  · simp [hn]
  have hlog : Nat.log 2 (3 * n) ≤ Nat.log 2 (n * 4) := by
    apply Nat.log_mono_right
    omega
  have hfour : Nat.log 2 (n * 4) = Nat.log 2 n + 2 := by
    rw [show n * 4 = (n * 2) * 2 by omega]
    rw [Nat.log_mul_base Nat.one_lt_two (mul_ne_zero hn (by omega))]
    rw [Nat.log_mul_base Nat.one_lt_two hn]
  omega

theorem core_prefixCount_le (gen : FeedbackGenerator) (n : ℕ) :
    (diagonalOrdered gen).prefixCount core n ≤ 3 + Nat.log2 n :=
  (core_prefixCount_le_log gen n).trans (log_three_mul_le n)

theorem diagonal_core_upperDensity_zero (gen : FeedbackGenerator) :
    (diagonalOrdered gen).upperDensity core = 0 := by
  have hbound : ∀ n,
      (diagonalOrdered gen).prefixRatio core n ≤
        ((3 + Nat.log2 n : ℕ) : ℝ) / (n : ℝ) := by
    intro n
    by_cases hn : n = 0
    · simp [hn]
    simp only [GenLimit.KleinbergWei.OrderedLanguage.prefixRatio, hn, if_false]
    apply div_le_div_of_nonneg_right
    · exact_mod_cast core_prefixCount_le gen n
    · positivity
  have htendsto : Tendsto ((diagonalOrdered gen).prefixRatio core)
      atTop (nhds 0) := by
    apply squeeze_zero
      (fun n => (diagonalOrdered gen).prefixRatio_nonneg core n) hbound
    exact GenLimit.tendsto_countingError_div 3
  exact htendsto.limsup_eq

end Stage3Work
