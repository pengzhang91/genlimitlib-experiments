import Stage3Model
import GenLimit.Paper10_UnionClosednessOfLanguageGeneration.Cardinality

open Set

namespace Stage3S2B

private def encode (A : Set ℕ) : Language :=
  core ∪ {z | ∃ n ∈ A, z = 2 * n + 3}

private theorem oddCode_not_core (n : ℕ) : 2 * n + 3 ∉ core := by
  rintro ⟨k, hk⟩
  have hodd : Odd (2 * n + 3) := ⟨n + 1, by omega⟩
  have hpow : 2 ^ k = 1 ∨ Even (2 ^ k) := by
    cases k with
    | zero => simp
    | succ k =>
        right
        exact ⟨2 ^ k, by rw [Nat.pow_succ, mul_two]⟩
  rcases hpow with hpow | hpow
  · simp only [hpow] at hk
    omega
  · rw [← hk] at hodd
    exact (Nat.not_even_iff_odd.mpr hodd) hpow

private theorem encode_mem_targetClass (A : Set ℕ) : encode A ∈ targetClass := by
  refine ⟨{z | ∃ n ∈ A, z = 2 * n + 3}, ?_, rfl⟩
  intro z hz
  rcases hz with ⟨n, hn, rfl⟩
  exact oddCode_not_core n

private theorem encode_injective : Function.Injective encode := by
  intro A B hAB
  ext n
  have hcode (C : Set ℕ) : 2 * n + 3 ∈ encode C ↔ n ∈ C := by
    constructor
    · intro h
      rcases h with hcore | ⟨m, hm, heq⟩
      · exact (oddCode_not_core n hcore).elim
      · have : m = n := by omega
        simpa [this] using hm
    · intro hn
      exact Or.inr ⟨n, hn, rfl⟩
  rw [← hcode A, hAB, hcode B]

private theorem targetClass_not_countable : ¬ targetClass.Countable := by
  intro h
  haveI : Countable targetClass := h
  let lift : Set ℕ → targetClass := fun A => ⟨encode A, encode_mem_targetClass A⟩
  have hlift : Function.Injective lift := by
    intro A B hAB
    apply encode_injective
    exact congrArg Subtype.val hAB
  have : Countable (Set ℕ) := hlift.countable
  exact GenLimit.UnionClosedness.powerSet_not_countable ℕ this

private theorem uniform_generation : UniformlyGeneratableWithoutSamples := by
  refine ⟨fun t => 2 ^ t, ?_, 0, ?_⟩
  · exact Nat.pow_right_injective (by omega)
  · intro K hK t ht
    rcases hK with ⟨A, hA, rfl⟩
    exact Or.inl ⟨t, rfl⟩

end Stage3S2B

-- The exact entry point is completed after the negative-witness construction.

theorem stage3_positive :
    ¬ Stage3S2B.targetClass.Countable ∧
      Stage3S2B.UniformlyGeneratableWithoutSamples := by
  exact ⟨Stage3S2B.targetClass_not_countable, Stage3S2B.uniform_generation⟩
