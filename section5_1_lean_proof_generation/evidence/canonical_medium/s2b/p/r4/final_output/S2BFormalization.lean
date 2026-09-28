import Stage3Model
import Mathlib.Data.Nat.Nth
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Set Filter

namespace Stage3Work

open Stage3S2B

def code (n : ℕ) : ℕ := 2 * n + 3

lemma code_not_core (n : ℕ) : code n ∉ core := by
  rintro ⟨k, hk⟩
  rcases k with _ | k
  · simp [code] at hk
  · simp [pow_succ, code] at hk
    omega

lemma code_injective : Function.Injective code := by
  intro a b h
  simp [code] at h
  omega

def encodedTarget (A : Set ℕ) : Language := core ∪ code '' A

lemma encodedTarget_mem (A : Set ℕ) : encodedTarget A ∈ targetClass := by
  refine ⟨code '' A, ?_, rfl⟩
  rintro z ⟨n, -, rfl⟩
  exact code_not_core n

lemma encodedTarget_injective : Function.Injective encodedTarget := by
  intro A B h
  ext n
  have hn : code n ∉ core := code_not_core n
  constructor <;> intro hnA
  · have hx : code n ∈ encodedTarget B := h ▸ (Or.inr ⟨n, hnA, rfl⟩)
    rcases hx with hc | ⟨m, hm, hmn⟩
    · exact (hn hc).elim
    · exact (code_injective hmn).symm ▸ hm
  · have hx : code n ∈ encodedTarget A := h.symm ▸ (Or.inr ⟨n, hnA, rfl⟩)
    rcases hx with hc | ⟨m, hm, hmn⟩
    · exact (hn hc).elim
    · exact (code_injective hmn).symm ▸ hm

lemma targetClass_uncountable : ¬ targetClass.Countable := by
  intro h
  have hne : targetClass.Nonempty := ⟨encodedTarget ∅, encodedTarget_mem ∅⟩
  rcases h.exists_surjective hne with ⟨f, hf⟩
  let A : Set ℕ := {n | code n ∉ (f n : Language)}
  have hmem : encodedTarget A ∈ targetClass := encodedTarget_mem A
  rcases hf ⟨encodedTarget A, hmem⟩ with ⟨m, hm⟩
  have hcode : code m ∈ encodedTarget A ↔ m ∈ A := by
    constructor
    · rintro (hc | ⟨n, hn, heq⟩)
      · exact (code_not_core m hc).elim
      · exact code_injective heq ▸ hn
    · intro ha
      exact Or.inr ⟨m, ha, rfl⟩
  simp only [A, Set.mem_setOf_eq] at hcode
  have hm' : (f m : Language) = encodedTarget A := congrArg Subtype.val hm
  rw [hm'] at hcode
  by_cases hp : code m ∈ encodedTarget A
  · exact (hcode.mp hp) hp
  · exact hp (hcode.mpr hp)

lemma uniform_generation : UniformlyGeneratableWithoutSamples := by
  refine ⟨fun t => 2 ^ t, ?_, 0, ?_⟩
  · exact Nat.pow_right_injective (by norm_num : 1 < (2 : ℕ))
  · intro K hK t ht
    rcases hK with ⟨A, hA, rfl⟩
    exact Or.inl ⟨t, rfl⟩

end Stage3Work

theorem stage3_positive :
    ¬ Stage3S2B.targetClass.Countable ∧
      Stage3S2B.UniformlyGeneratableWithoutSamples := by
  exact ⟨Stage3Work.targetClass_uncountable, Stage3Work.uniform_generation⟩

theorem stage3_result_of_negative (hneg : Stage3S2B.NegativeClaim) :
    Stage3S2B.MainClaim := by
  exact ⟨Stage3Work.targetClass_uncountable, Stage3Work.uniform_generation, hneg⟩
