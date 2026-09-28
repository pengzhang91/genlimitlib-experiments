import Stage3Model
import GenLimit.Paper10_UnionClosednessOfLanguageGeneration.Cardinality
import Adversary

open Set

namespace Stage3S2B

lemma pow_two_injective : Function.Injective (fun k : ℕ => 2 ^ k) := by
  intro a b hab
  exact (Nat.pow_right_injective (by omega : 1 < 2)) hab

lemma core_infinite : core.Infinite := by
  exact Set.infinite_range_of_injective pow_two_injective

lemma ordinary_infinite : ordinary.Infinite := by
  have hodd : Set.range (fun n : ℕ => 2 * n + 3) ⊆ ordinary := by
    intro z hz
    obtain ⟨n, rfl⟩ := hz
    intro hcore
    obtain ⟨k, hk⟩ := hcore
    dsimp at hk
    cases k with
    | zero => simp at hk
    | succ k =>
        have heven : Even (2 ^ (Nat.succ k)) := by
          exact Nat.even_pow.mpr ⟨even_two, by omega⟩
        have heven' : Even (2 * n + 3) := by
          rw [← hk]
          exact heven
        have hodd' : Odd (2 * n + 3) := ⟨n + 1, by omega⟩
        obtain ⟨a, ha⟩ := heven'
        obtain ⟨b, hb⟩ := hodd'
        omega
  have hinj : Function.Injective (fun n : ℕ => 2 * n + 3) := by
    intro a b hab
    dsimp at hab
    omega
  exact (Set.infinite_range_of_injective hinj).mono hodd

lemma targetClass_not_countable : ¬ targetClass.Countable := by
  intro hcount
  let encode : Set ordinary → Language := fun A => core ∪ ((fun z : ordinary => (z : ℕ)) '' A)
  have hmem : ∀ A : Set ordinary, encode A ∈ targetClass := by
    intro A
    refine ⟨(fun z : ordinary => (z : ℕ)) '' A, ?_, rfl⟩
    intro z hz
    obtain ⟨w, hw, rfl⟩ := hz
    exact w.property
  have hinj : Function.Injective encode := by
    intro A B hAB
    ext z
    have hzord : (z : ℕ) ∈ ordinary := z.property
    have hznot : (z : ℕ) ∉ core := hzord
    have := Set.ext_iff.mp hAB (z : ℕ)
    simpa [encode, hznot] using this
  have hrange : Set.range encode ⊆ targetClass := by
    intro K hK
    obtain ⟨A, rfl⟩ := hK
    exact hmem A
  have hcountRange : (Set.range encode).Countable := hcount.mono hrange
  letI : Countable (Set.range encode) := hcountRange.to_subtype
  let rangeEncode : Set ordinary → Set.range encode :=
    fun A => ⟨encode A, ⟨A, rfl⟩⟩
  have hrangeInj : Function.Injective rangeEncode := by
    intro A B hAB
    exact hinj (Subtype.ext_iff.mp hAB)
  have hcountType : Countable (Set ordinary) := hrangeInj.countable
  letI : Infinite ordinary := Set.infinite_coe_iff.mpr ordinary_infinite
  exact GenLimit.UnionClosedness.powerSet_not_countable ordinary hcountType

lemma uniformly_generatable : UniformlyGeneratableWithoutSamples := by
  refine ⟨fun k => 2 ^ k, pow_two_injective, 0, ?_⟩
  intro K hK t ht
  obtain ⟨A, hA, rfl⟩ := hK
  exact Set.mem_union_left A ⟨t, rfl⟩

end Stage3S2B

theorem stage3_result : Stage3S2B.MainClaim := by
  refine ⟨Stage3S2B.targetClass_not_countable, Stage3S2B.uniformly_generatable, ?_⟩
  exact Stage3S2B.Hist.negative_claim
