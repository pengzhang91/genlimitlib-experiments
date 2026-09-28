import S2BFormalization

open Set Filter
open Stage3S2B
open Stage3Proof

namespace Stage3Proof

theorem core_prefixCount_bound (gen : FeedbackGenerator) (n : ℕ) :
    (orderedTarget gen).prefixCount core n ≤ Nat.log2 (12 * n + 10) + 1 := by
  classical
  let s := (Finset.range n).filter fun i => (orderedTarget gen).enumeration i ∈ core
  let e : ℕ → ℕ := fun i => Nat.log2 ((orderedTarget gen).enumeration i)
  have heinj : Set.InjOn e (s : Set ℕ) := by
    intro i hi j hj hij
    simp only [s, Finset.mem_coe, Finset.mem_filter] at hi hj
    rcases hi.2 with ⟨a, ha⟩
    rcases hj.2 with ⟨b, hb⟩
    have hab : a = b := by
      have hla : Nat.log2 ((orderedTarget gen).enumeration i) = a := by
        rw [← ha, Nat.log2_eq_log_two, Nat.log_pow (by omega : 1 < (2 : ℕ))]
      have hlb : Nat.log2 ((orderedTarget gen).enumeration j) = b := by
        rw [← hb, Nat.log2_eq_log_two, Nat.log_pow (by omega : 1 < (2 : ℕ))]
      calc
        a = e i := by simpa [e] using hla.symm
        _ = e j := hij
        _ = b := by simpa [e] using hlb
    apply (orderedTarget gen).enumeration_injective
    rw [← ha, ← hb, hab]
  have herange : s.image e ⊆ Finset.range (Nat.log2 (12 * n + 10) + 1) := by
    intro k hk
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hk
    simp only [s, Finset.mem_filter, Finset.mem_range] at hi
    have hbound := target_nth_bound gen i
    have hmono : Nat.log2 ((orderedTarget gen).enumeration i) ≤
        Nat.log2 (12 * n + 10) := by
      rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
      apply Nat.log_mono_right
      omega
    simp only [Finset.mem_range]
    dsimp only [e]
    exact Nat.lt_succ_of_le hmono
  change s.card ≤ _
  rw [← Finset.card_image_iff.mpr heinj]
  simpa using Finset.card_le_card herange

theorem core_prefixRatio_tendsto_zero (gen : FeedbackGenerator) :
    Tendsto ((orderedTarget gen).prefixRatio core) atTop (nhds 0) := by
  let error : ℕ → ℝ := fun n => ((6 + Nat.log2 n : ℕ) : ℝ) / (n : ℝ)
  have herror : Tendsto error atTop (nhds 0) := by
    simpa [error] using GenLimit.tendsto_countingError_div 6
  apply squeeze_zero (fun n => (orderedTarget gen).prefixRatio_nonneg core n) _ herror
  intro n
  by_cases hn : n = 0
  · simp [hn, error]
  · have hcount := core_prefixCount_bound gen n
    have hlinear : 12 * n + 10 ≤ 32 * n := by omega
    have hmul : ∀ m : ℕ, Nat.log 2 (n * 2 ^ m) = Nat.log 2 n + m := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
          rw [pow_succ, ← mul_assoc,
            Nat.log_mul_base (by omega : 1 < (2 : ℕ))
              (mul_ne_zero hn (pow_ne_zero m (by omega : (2 : ℕ) ≠ 0))), ih]
          omega
    have hlog : Nat.log2 (12 * n + 10) ≤ Nat.log2 n + 5 := by
      rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
      calc
        Nat.log 2 (12 * n + 10) ≤ Nat.log 2 (32 * n) := Nat.log_mono_right hlinear
        _ = Nat.log 2 (n * 2 ^ 5) := by congr 1 <;> omega
        _ = Nat.log 2 n + 5 := hmul 5
    simp only [GenLimit.KleinbergWei.OrderedLanguage.prefixRatio, hn, if_false]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
    exact_mod_cast hcount.trans (by omega : Nat.log2 (12 * n + 10) + 1 ≤ 6 + Nat.log2 n)

theorem core_upperDensity_zero (gen : FeedbackGenerator) :
    (orderedTarget gen).upperDensity core = 0 := by
  exact (core_prefixRatio_tendsto_zero gen).limsup_eq

end Stage3Proof
