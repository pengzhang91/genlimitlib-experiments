import Stage3Model
import GenLimit.Paper10_UnionClosednessOfLanguageGeneration.Cardinality

open Set

namespace Stage3S2BProof

open Stage3S2B

def ordinaryCode (n : ℕ) : ℕ := 2 * n + 3

theorem ordinaryCode_injective : Function.Injective ordinaryCode := by
  intro m n h
  simp [ordinaryCode] at h
  omega

theorem ordinaryCode_mem (n : ℕ) : ordinaryCode n ∈ ordinary := by
  intro hcore
  obtain ⟨k, hk⟩ := hcore
  cases k with
  | zero => simp [ordinaryCode] at hk
  | succ k =>
      simp [ordinaryCode, pow_succ] at hk
      omega

def encodedOrdinary (S : Set ℕ) : Language := ordinaryCode '' S

theorem encodedOrdinary_subset (S : Set ℕ) : encodedOrdinary S ⊆ ordinary := by
  rintro _ ⟨n, _hn, rfl⟩
  exact ordinaryCode_mem n

def encodedTarget (S : Set ℕ) : Language := core ∪ encodedOrdinary S

theorem encodedTarget_mem (S : Set ℕ) : encodedTarget S ∈ targetClass := by
  exact ⟨encodedOrdinary S, encodedOrdinary_subset S, rfl⟩

theorem encodedTarget_injective : Function.Injective encodedTarget := by
  intro S T hST
  ext n
  have hmem := Set.ext_iff.mp hST (ordinaryCode n)
  have hnotcore : ordinaryCode n ∉ core := ordinaryCode_mem n
  have himage (U : Set ℕ) : ordinaryCode n ∈ ordinaryCode '' U ↔ n ∈ U := by
    constructor
    · rintro ⟨m, hm, hmn⟩
      exact ordinaryCode_injective hmn ▸ hm
    · intro hn
      exact ⟨n, hn, rfl⟩
  simpa [encodedTarget, encodedOrdinary, hnotcore, himage] using hmem

theorem targetClass_uncountable : ¬ targetClass.Countable := by
  intro hcountable
  let f : Set ℕ → targetClass := fun S => ⟨encodedTarget S, encodedTarget_mem S⟩
  have hf : Function.Injective f := by
    intro S T h
    apply encodedTarget_injective
    exact congrArg Subtype.val h
  letI : Countable targetClass := hcountable.to_subtype
  have hpower : Countable (Set ℕ) := hf.countable
  exact GenLimit.UnionClosedness.powerSet_not_countable ℕ hpower

theorem uniform_generation : UniformlyGeneratableWithoutSamples := by
  refine ⟨fun t => 2 ^ t, ?_, 0, ?_⟩
  · intro m n h
    exact Nat.pow_right_injective (by omega) h
  · intro K hK t _ht
    obtain ⟨A, hA, rfl⟩ := hK
    exact Or.inl ⟨t, rfl⟩

theorem stage3_positive :
    ¬ targetClass.Countable ∧ UniformlyGeneratableWithoutSamples :=
  ⟨targetClass_uncountable, uniform_generation⟩

end Stage3S2BProof
