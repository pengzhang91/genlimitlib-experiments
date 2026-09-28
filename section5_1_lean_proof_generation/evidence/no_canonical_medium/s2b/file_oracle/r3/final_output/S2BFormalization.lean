import Helpers

open Stage3S2B

namespace Stage3Work

lemma odd_three_not_core (n : ℕ) : 2 * n + 3 ∉ core := by
  rintro ⟨k, hk⟩
  cases k with
  | zero => simp at hk
  | succ k =>
      have heven : Even (2 ^ (k + 1)) := by
        refine ⟨2 ^ k, by rw [pow_succ]; omega⟩
      have hodd : Odd (2 * n + 3) := by
        refine ⟨n + 1, by omega⟩
      change 2 ^ (k + 1) = 2 * n + 3 at hk
      rw [hk] at heven
      exact (Nat.not_even_iff_odd.mpr hodd) heven

def encode (A : Set ℕ) : Language :=
  core ∪ {z | ∃ n ∈ A, z = 2 * n + 3}

lemma encode_mem_targetClass (A : Set ℕ) : encode A ∈ targetClass := by
  refine ⟨{z | ∃ n ∈ A, z = 2 * n + 3}, ?_, rfl⟩
  rintro z ⟨n, hn, rfl⟩
  exact odd_three_not_core n

lemma encode_injective : Function.Injective encode := by
  intro A B h
  ext n
  have hncore := odd_three_not_core n
  have hA : (2 * n + 3 ∈ encode A) ↔ n ∈ A := by
    constructor
    · intro hmem
      rcases hmem with hmem | ⟨m, hm, heq⟩
      · exact (odd_three_not_core n hmem).elim
      · have hmn : m = n := by omega
        simpa [hmn] using hm
    · intro hn
      exact Or.inr ⟨n, hn, rfl⟩
  have hB : (2 * n + 3 ∈ encode B) ↔ n ∈ B := by
    constructor
    · intro hmem
      rcases hmem with hmem | ⟨m, hm, heq⟩
      · exact (odd_three_not_core n hmem).elim
      · have hmn : m = n := by omega
        simpa [hmn] using hm
    · intro hn
      exact Or.inr ⟨n, hn, rfl⟩
  rw [← hA, h, hB]

lemma targetClass_not_countable : ¬ targetClass.Countable := by
  intro hc
  have hpre : (encode ⁻¹' targetClass).Countable :=
    hc.preimage encode_injective
  have hall : encode ⁻¹' targetClass = Set.univ := by
    ext A
    simp [encode_mem_targetClass]
  rw [hall] at hpre
  haveI : Countable (Set ℕ) := Set.countable_univ_iff.mp hpre
  exact GenLimit.UnionClosedness.powerSet_not_countable ℕ inferInstance

lemma core_injective : Function.Injective (fun k : ℕ => 2 ^ k) := by
  have hmono : StrictMono (fun k : ℕ => 2 ^ k) := by
    intro a b hab
    exact Nat.pow_lt_pow_right (by omega) hab
  exact hmono.injective

lemma uniformly_generatable : UniformlyGeneratableWithoutSamples := by
  refine ⟨fun k => 2 ^ k, core_injective, 0, ?_⟩
  intro K hK t ht
  rcases hK with ⟨A, hA, rfl⟩
  exact Or.inl ⟨t, rfl⟩

 theorem positive_claims :
    ¬ targetClass.Countable ∧ UniformlyGeneratableWithoutSamples :=
  ⟨targetClass_not_countable, uniformly_generatable⟩

end Stage3Work
