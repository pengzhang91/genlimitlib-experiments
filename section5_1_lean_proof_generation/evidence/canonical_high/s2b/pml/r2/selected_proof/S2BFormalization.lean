import Density

open Set

namespace Stage3Proof

open Stage3S2B

lemma targetClass_uncountable : ¬ targetClass.Countable := by
  letI : Infinite ordinary := ordinary_infinite.to_subtype
  intro hcountable
  let f : Set ordinary → targetClass :=
    fun A =>
      ⟨core ∪ ((fun z : ordinary => z.1) '' A),
        ⟨(fun z : ordinary => z.1) '' A,
          by
            rintro z ⟨p, _hp, rfl⟩
            exact p.2,
          rfl⟩⟩
  have hf : Function.Injective f := by
    intro A B hAB
    apply Set.ext
    intro p
    have hpNotCore : p.1 ∉ core := p.2
    have hpImage (C : Set ordinary) :
        p.1 ∈ (fun z : ordinary => z.1) '' C ↔ p ∈ C := by
      constructor
      · rintro ⟨q, hq, hqp⟩
        have hqEq : q = p := Subtype.ext hqp
        simpa [hqEq] using hq
      · intro hp
        exact ⟨p, hp, rfl⟩
    have hmem := Set.ext_iff.mp (congrArg Subtype.val hAB) p.1
    change
      p.1 ∈ core ∪ (fun z : ordinary => z.1) '' A ↔
        p.1 ∈ core ∪ (fun z : ordinary => z.1) '' B at hmem
    rw [Set.mem_union, Set.mem_union, hpImage, hpImage] at hmem
    simpa [hpNotCore] using hmem
  letI : Countable targetClass := hcountable.to_subtype
  have hpower : Countable (Set ordinary) := hf.countable
  exact GenLimit.UnionClosedness.powerSet_not_countable ordinary hpower

end Stage3Proof

open Stage3S2B Stage3Proof

theorem stage3_result : Stage3S2B.MainClaim := by
  refine ⟨targetClass_uncountable, ?_, ?_⟩
  · refine ⟨fun t => 2 ^ t, Nat.pow_right_injective (by omega), 0, ?_⟩
    intro K hK t _ht
    obtain ⟨A, _hA, rfl⟩ := hK
    exact Or.inl ⟨t, rfl⟩
  · intro gen _hvalid
    refine ⟨target gen, target_mem_class gen, presenter, transcript gen,
      orderedTarget gen, ?_⟩
    exact ⟨rfl, orderedTarget_inherits gen, presented_by gen,
      follows_protocol gen, clean_presentation gen, presentation_injective gen,
      presentation_complete gen, orderedTarget_scored_upperDensity_zero gen⟩
