import Stage3Model
import Diagonal

open Set

namespace Stage3Work

open Stage3S2B

lemma ordinary_infinite : ordinary.Infinite := by
  let f : ℕ → ℕ := fun n => 2 * n + 3
  have hf : Function.Injective f := by
    intro a b h
    dsimp [f] at h
    omega
  have hr : Set.range f ⊆ ordinary := by
    rintro z ⟨n, rfl⟩
    intro hz
    rcases hz with ⟨k, hk⟩
    cases k with
    | zero =>
        change 1 = 2 * n + 3 at hk
        omega
    | succ k =>
        change 2 ^ (k + 1) = 2 * n + 3 at hk
        rw [pow_succ] at hk
        omega
  exact Set.Infinite.mono hr (Set.infinite_range_of_injective hf)

lemma powerset_not_countable (β : Type*) [Infinite β] [Countable β] :
    ¬ Countable (Set β) := by
  intro hcountable
  letI : Countable (Set β) := hcountable
  let den : Denumerable β := Classical.choice (nonempty_denumerable β)
  let e : ℕ ≃ β := (@Denumerable.eqv β den).symm
  obtain ⟨f, hf⟩ :=
    (countable_iff_exists_surjective (α := Set β)).mp hcountable
  let diagonal : Set β := {p | p ∉ f (e.symm p)}
  obtain ⟨n, hn⟩ := hf diagonal
  let p : β := e n
  have hdiag : p ∈ diagonal ↔ p ∉ diagonal := by
    have hep : e.symm p = n := by simp [p]
    constructor
    · intro hp
      change p ∉ f (e.symm p) at hp
      rw [hep, hn] at hp
      exact hp
    · intro hp
      change p ∉ f (e.symm p)
      rw [hep, hn]
      exact hp
  by_cases hp : p ∈ diagonal
  · exact (hdiag.mp hp) hp
  · exact hp (hdiag.mpr hp)

lemma targetClass_not_countable : ¬ targetClass.Countable := by
  intro hc
  letI : Infinite ordinary := ordinary_infinite.to_subtype
  let encode : Set ordinary → targetClass := fun A =>
    ⟨core ∪ ((fun z : ordinary => z.1) '' A),
      ⟨(fun z : ordinary => z.1) '' A,
        by rintro _ ⟨z, _, rfl⟩; exact z.2,
        rfl⟩⟩
  have hencode : Function.Injective encode := by
    intro A B hAB
    apply Set.ext
    intro z
    have hsets := congrArg Subtype.val hAB
    have hznot : z.1 ∉ core := z.2
    have himage (C : Set ordinary) :
        z.1 ∈ (fun w : ordinary => w.1) '' C ↔ z ∈ C := by
      constructor
      · rintro ⟨w, hw, hval⟩
        have : w = z := Subtype.ext hval
        simpa [this] using hw
      · intro hz
        exact ⟨z, hz, rfl⟩
    have hm := Set.ext_iff.mp hsets z.1
    change z.1 ∈ core ∪ ((fun w : ordinary => w.1) '' A) ↔
      z.1 ∈ core ∪ ((fun w : ordinary => w.1) '' B) at hm
    simp only [Set.mem_union, hznot, false_or, himage] at hm
    exact hm
  letI : Countable targetClass := hc.to_subtype
  have hp : Countable (Set ordinary) := hencode.countable
  exact powerset_not_countable ordinary hp

lemma uniform_generation : UniformlyGeneratableWithoutSamples := by
  refine ⟨fun t => 2 ^ t, Nat.pow_right_injective (by omega), 0, ?_⟩
  intro K hK t _
  rcases hK with ⟨A, hA, rfl⟩
  exact Or.inl ⟨t, rfl⟩

end Stage3Work

open Stage3Work

theorem stage3_result : Stage3S2B.MainClaim := by
  exact ⟨targetClass_not_countable, uniform_generation, negative_claim⟩
