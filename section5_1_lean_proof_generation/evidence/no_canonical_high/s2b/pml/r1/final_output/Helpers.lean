import Stage3Model
import GenLimit.Paper10_UnionClosednessOfLanguageGeneration.Cardinality

namespace Stage3Work

open Stage3S2B

private def code (n : ℕ) : ℕ := 2 * n + 3

private theorem code_mem_ordinary (n : ℕ) : code n ∈ ordinary := by
  intro h
  rcases h with ⟨k, hk⟩
  cases k with
  | zero => simp [code] at hk
  | succ k =>
      simp only [pow_succ] at hk
      dsimp [code] at hk
      omega

private theorem code_injective : Function.Injective code := by
  intro m n h
  dsimp [code] at h
  omega

private def encoded (S : Set ℕ) : Language :=
  core ∪ code '' S

private theorem encoded_mem (S : Set ℕ) : encoded S ∈ targetClass := by
  refine ⟨code '' S, ?_, rfl⟩
  rintro z ⟨n, hn, rfl⟩
  exact code_mem_ordinary n

private theorem encoded_injective : Function.Injective encoded := by
  intro S T hST
  ext n
  have hprobe := Set.ext_iff.mp hST (code n)
  have hnotcore : code n ∉ core := code_mem_ordinary n
  simp only [encoded, Set.mem_union, hnotcore, false_or, Set.mem_image] at hprobe
  constructor
  · intro hn
    have : code n ∈ code '' T := hprobe.mp ⟨n, hn, rfl⟩
    rcases this with ⟨m, hm, hmn⟩
    exact (code_injective hmn).symm ▸ hm
  · intro hn
    have : code n ∈ code '' S := hprobe.mpr ⟨n, hn, rfl⟩
    rcases this with ⟨m, hm, hmn⟩
    exact (code_injective hmn).symm ▸ hm

 theorem targetClass_uncountable : ¬ targetClass.Countable := by
  intro hcountable
  let f : Set ℕ → targetClass := fun S => ⟨encoded S, encoded_mem S⟩
  have hf : Function.Injective f := by
    intro S T h
    apply encoded_injective
    exact congrArg Subtype.val h
  letI : Countable targetClass := hcountable.to_subtype
  have hpower : Countable (Set ℕ) := hf.countable
  exact GenLimit.UnionClosedness.powerSet_not_countable ℕ hpower

 theorem uniform_generation : UniformlyGeneratableWithoutSamples := by
  refine ⟨fun k => 2 ^ k, Nat.pow_right_injective (by omega), 0, ?_⟩
  intro K hK t ht
  rcases hK with ⟨A, hA, rfl⟩
  exact Or.inl ⟨t, rfl⟩

end Stage3Work
