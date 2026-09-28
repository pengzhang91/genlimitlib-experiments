import Stage3Model
import GenLimit.Paper10_UnionClosednessOfLanguageGeneration.Cardinality

open Set Filter

namespace Stage3S2BProof

open Stage3S2B

lemma core_mem_pow (t : ℕ) : 2 ^ t ∈ core := ⟨t, rfl⟩

lemma pow_two_injective : Function.Injective (fun t : ℕ => 2 ^ t) := by
  intro a b h
  exact (Nat.pow_right_injective (by omega : 1 < 2)) h

lemma targetClass_uncountable : ¬ targetClass.Countable := by
  intro hcountable
  let encode : Set ℕ → targetClass := fun A =>
    ⟨core ∪ (A ∩ ordinary), ⟨A ∩ ordinary, inter_subset_right, rfl⟩⟩
  let probe : ℕ → ℕ := fun n => 2 * n + 3
  have hprobeOrdinary : ∀ n, probe n ∈ ordinary := by
    intro n
    simp only [probe, ordinary, mem_compl_iff, core, mem_range]
    rintro ⟨k, hk⟩
    cases k with
    | zero => norm_num at hk
    | succ k =>
        simp only [pow_succ] at hk
        omega
  let restrict : Set ℕ → Set ℕ := fun A => probe '' A
  have hrestrict : Function.Injective restrict := by
    intro A B hAB
    apply Set.ext
    intro n
    have hp : Function.Injective probe := by
      intro a b hab
      dsimp [probe] at hab
      omega
    constructor <;> intro hn
    · have : probe n ∈ restrict A := ⟨n, hn, rfl⟩
      rw [hAB] at this
      rcases this with ⟨m, hm, hmn⟩
      exact hp hmn ▸ hm
    · have : probe n ∈ restrict B := ⟨n, hn, rfl⟩
      rw [← hAB] at this
      rcases this with ⟨m, hm, hmn⟩
      exact hp hmn ▸ hm
  have hencode : Function.Injective (encode ∘ restrict) := by
    intro A B hAB
    apply hrestrict
    apply Set.ext
    intro z
    have hzOrd : z ∈ restrict A → z ∈ ordinary := by
      rintro ⟨n, hn, rfl⟩
      exact hprobeOrdinary n
    have hzOrdB : z ∈ restrict B → z ∈ ordinary := by
      rintro ⟨n, hn, rfl⟩
      exact hprobeOrdinary n
    have hv := congrArg Subtype.val hAB
    have hm := Set.ext_iff.mp hv z
    simp only [Function.comp_apply, encode, mem_union, mem_inter_iff] at hm
    constructor
    · intro hz
      rcases hz with ⟨n, hn, rfl⟩
      have hnot : probe n ∉ core := hprobeOrdinary n
      exact (hm.mp (Or.inr ⟨⟨n, hn, rfl⟩, hnot⟩)).resolve_left hnot |>.1
    · intro hz
      rcases hz with ⟨n, hn, rfl⟩
      have hnot : probe n ∉ core := hprobeOrdinary n
      exact (hm.mpr (Or.inr ⟨⟨n, hn, rfl⟩, hnot⟩)).resolve_left hnot |>.1
  letI : Countable targetClass := hcountable.to_subtype
  have hpowerset : Countable (Set ℕ) := hencode.countable
  exact GenLimit.UnionClosedness.powerSet_not_countable ℕ hpowerset

lemma uniform_positive : UniformlyGeneratableWithoutSamples := by
  refine ⟨fun t => 2 ^ t, pow_two_injective, 0, ?_⟩
  intro K hK t _
  rcases hK with ⟨A, hA, rfl⟩
  exact Or.inl (core_mem_pow t)


end Stage3S2BProof

open Stage3S2B Stage3S2BProof

/-- Checked independent clauses of the fixed main claim. -/
theorem stage3_uncountable_and_uniform :
    ¬ Stage3S2B.targetClass.Countable ∧
      Stage3S2B.UniformlyGeneratableWithoutSamples :=
  ⟨targetClass_uncountable, uniform_positive⟩
