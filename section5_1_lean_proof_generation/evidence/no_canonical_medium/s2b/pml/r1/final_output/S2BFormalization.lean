import Stage3Model
import Diagonal
import GenLimit.Paper10_UnionClosednessOfLanguageGeneration.Cardinality

open Set

namespace Stage3Work

open Stage3S2B

private def code (n : ℕ) : ℕ := 2 * n + 3

private theorem code_injective : Function.Injective code := by
  intro m n h
  simp only [code] at h
  omega

private theorem code_ordinary (n : ℕ) : code n ∈ ordinary := by
  intro h
  rcases h with ⟨k, hk⟩
  cases k with
  | zero => simp [code] at hk
  | succ k =>
      change 2 ^ (k + 1) = code n at hk
      rw [pow_succ] at hk
      simp only [code] at hk
      omega

private def encoded (A : Set ℕ) : Language :=
  core ∪ code '' A

private theorem encoded_mem_targetClass (A : Set ℕ) :
    encoded A ∈ targetClass := by
  refine ⟨code '' A, ?_, rfl⟩
  rintro z ⟨n, hn, rfl⟩
  exact code_ordinary n

private theorem encoded_injective : Function.Injective encoded := by
  intro A B h
  ext n
  constructor
  · intro hn
    have hc : code n ∈ encoded A := by
      exact Or.inr ⟨n, hn, rfl⟩
    rw [h] at hc
    rcases hc with hc | hc
    · exact False.elim (code_ordinary n hc)
    · rcases hc with ⟨m, hm, heq⟩
      have hmn : m = n := code_injective heq
      exact hmn ▸ hm
  · intro hn
    have hc : code n ∈ encoded B := by
      exact Or.inr ⟨n, hn, rfl⟩
    rw [← h] at hc
    rcases hc with hc | hc
    · exact False.elim (code_ordinary n hc)
    · rcases hc with ⟨m, hm, heq⟩
      have hmn : m = n := code_injective heq
      exact hmn ▸ hm

private theorem targetClass_uncountable : ¬ targetClass.Countable := by
  intro hcount
  letI : Encodable targetClass := hcount.toEncodable
  let embed : Set ℕ → targetClass := fun A => ⟨encoded A, encoded_mem_targetClass A⟩
  have hembed : Function.Injective embed := by
    intro A B h
    apply encoded_injective
    exact Subtype.ext_iff.mp h
  have : Countable (Set ℕ) :=
    (countable_iff_exists_injective (Set ℕ)).2
      ⟨fun A => Encodable.encode (embed A),
        Encodable.encode_injective.comp hembed⟩
  exact GenLimit.UnionClosedness.powerSet_not_countable ℕ this

private theorem uniform_core_generation : UniformlyGeneratableWithoutSamples := by
  refine ⟨fun k => 2 ^ k, Nat.pow_right_injective (by omega), 0, ?_⟩
  intro K hK t ht
  rcases hK with ⟨A, hA, rfl⟩
  exact Or.inl ⟨t, rfl⟩

private theorem negative_claim : NegativeClaim :=
  diagonal_negative_claim

theorem result : MainClaim := by
  exact ⟨targetClass_uncountable, uniform_core_generation, negative_claim⟩

end Stage3Work

theorem stage3_result : Stage3S2B.MainClaim := Stage3Work.result
