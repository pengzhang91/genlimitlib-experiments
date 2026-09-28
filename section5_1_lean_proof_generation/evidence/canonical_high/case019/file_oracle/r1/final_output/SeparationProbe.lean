import output.CountableProof
import GenLimit.Paper12_NoiseLossAndFeedback.FiniteNoiseSeparation
import GenLimit.Paper10_UnionClosednessOfLanguageGeneration.Cardinality

open Set
open Stage3Case019

namespace Case019

open GenLimit.UnionClosedness

@[simp] theorem balanced_negative (n : ℕ) : balanced (2*n+1) = negativeCode n := by
  unfold balanced negativeCode
  simp [Nat.add_mod, Nat.mul_mod, Nat.add_div]

@[simp] theorem balanced_positive (n : ℕ) : balanced (2*n+2) = positiveCode n := by
  unfold balanced positiveCode
  simp [Nat.add_mod, Nat.mul_mod, Nat.add_div]
  congr
  omega

theorem balanced_surjective : Function.Surjective balanced := by
  intro z
  rcases z with n | n
  · cases n with
    | zero => exact ⟨0, rfl⟩
    | succ n => exact ⟨2*n+2, balanced_positive n⟩
  · exact ⟨2*n+1, balanced_negative n⟩

theorem balanced_injective : Function.Injective balanced := by
  intro m n h
  rcases Nat.even_or_odd' m with ⟨k, rfl⟩ | ⟨k, rfl⟩ <;>
    rcases Nat.even_or_odd' n with ⟨l, rfl⟩ | ⟨l, rfl⟩
  · cases k with
    | zero =>
        cases l with
        | zero => rfl
        | succ l => simp [balanced_positive] at h
    | succ k =>
        cases l with
        | zero => simp [balanced_positive] at h
        | succ l =>
            simp only [show 2 * (k+1) = 2*k+2 by omega,
              show 2 * (l+1) = 2*l+2 by omega, balanced_positive] at h
            have := positiveCode_injective h
            omega
  · cases k with
    | zero => simp [balanced_negative] at h
    | succ k =>
        simp only [show 2 * (k+1) = 2*k+2 by omega,
          balanced_positive, balanced_negative] at h
        omega
  · cases l with
    | zero => simp [balanced_negative] at h
    | succ l =>
        simp only [show 2 * (l+1) = 2*l+2 by omega,
          balanced_positive, balanced_negative] at h
        omega
  · simp only [balanced_negative] at h
    have := negativeCode_injective h
    omega

noncomputable def balancedEquiv : ℕ ≃ ℤ :=
  Equiv.ofBijective balanced ⟨balanced_injective, balanced_surjective⟩

@[simp] theorem balancedEquiv_apply (n : ℕ) : balancedEquiv n = balanced n := rfl

end Case019
