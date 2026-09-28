import Stage3Model
import GenLimit.Paper10_UnionClosednessOfLanguageGeneration.Cardinality
import Adversary

open Set

namespace Stage3S2B

theorem ordinary_infinite : ordinary.Infinite := by
  have hodd : Set.range (fun n : ℕ => 2 * n + 3) ⊆ ordinary := by
    rintro z ⟨n, rfl⟩
    intro hcore
    obtain ⟨k, hk⟩ := hcore
    have hodd : Odd (2 * n + 3) := ⟨n + 1, by omega⟩
    cases k with
    | zero => norm_num at hk
    | succ k =>
        change 2 ^ (k + 1) = 2 * n + 3 at hk
        have heven : Even (2 ^ (k + 1)) := by
          refine ⟨2 ^ k, by ring⟩
        rw [hk] at heven
        exact (Nat.not_even_iff_odd.mpr hodd) heven
  apply (Set.infinite_range_of_injective ?_).mono hodd
  intro a b hab
  change 2 * a + 3 = 2 * b + 3 at hab
  omega

theorem targetClass_not_countable : ¬ targetClass.Countable := by
  letI : Infinite ordinary := ordinary_infinite.to_subtype
  intro hcount
  let encode : Set ordinary → targetClass := fun A =>
    ⟨core ∪ ((fun z : ordinary => z.1) '' A),
      ⟨(fun z : ordinary => z.1) '' A,
        by rintro _ ⟨z, _, rfl⟩; exact z.2,
        rfl⟩⟩
  have hencode : Function.Injective encode := by
    intro A B hAB
    apply Set.ext
    intro z
    have hzordinary : z.1 ∉ core := z.2
    have hzimage (C : Set ordinary) :
        z.1 ∈ (fun w : ordinary => w.1) '' C ↔ z ∈ C := by
      constructor
      · rintro ⟨w, hw, hwz⟩
        simpa [Subtype.ext hwz] using hw
      · intro hz
        exact ⟨z, hz, rfl⟩
    have hm := Set.ext_iff.mp (congrArg Subtype.val hAB) z.1
    change z.1 ∈ core ∪ ((fun w : ordinary => w.1) '' A) ↔
      z.1 ∈ core ∪ ((fun w : ordinary => w.1) '' B) at hm
    simpa [hzordinary, hzimage] using hm
  letI : Countable targetClass := hcount.to_subtype
  have hpowers : Countable (Set ordinary) := hencode.countable
  exact GenLimit.UnionClosedness.powerSet_not_countable ordinary hpowers

theorem uniformlyGeneratableWithoutSamples :
    UniformlyGeneratableWithoutSamples := by
  refine ⟨fun k => 2 ^ k, ?_, 0, ?_⟩
  · intro a b hab
    exact Nat.pow_right_injective (by norm_num) hab
  · intro K hK t _
    obtain ⟨A, hA, rfl⟩ := hK
    exact Or.inl ⟨t, rfl⟩

end Stage3S2B

theorem stage3_result : Stage3S2B.MainClaim := by
  refine ⟨Stage3S2B.targetClass_not_countable,
    Stage3S2B.uniformlyGeneratableWithoutSamples, ?_⟩
  exact Stage3S2B.negativeClaim
