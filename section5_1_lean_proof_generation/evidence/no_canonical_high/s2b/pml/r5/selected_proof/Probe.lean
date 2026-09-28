import «output/S2BFormalization»

open Set
open S2BProof
open Stage3S2B

theorem probe : Stage3S2B.MainClaim := by
  refine ⟨?_, ?_, ?_⟩
  · intro hcountable
    let encode : Set ℕ → targetClass := fun A =>
      ⟨core ∪ oddCode '' A, by
        refine ⟨oddCode '' A, ?_, rfl⟩
        intro z hz
        obtain ⟨i, _, rfl⟩ := hz
        exact oddCode_not_core i⟩
    have hencode : Function.Injective encode := by
      intro A B hAB
      apply Set.ext
      intro i
      have hprobe := Set.ext_iff.mp (congrArg Subtype.val hAB) (oddCode i)
      simp only [encode, Set.mem_union, Set.mem_image] at hprobe
      simp only [oddCode_not_core, false_or] at hprobe
      constructor
      · intro hi
        have : oddCode i ∈ oddCode '' B := hprobe.mp ⟨i, hi, rfl⟩
        obtain ⟨j, hj, hji⟩ := this
        exact (oddCode_injective hji).symm ▸ hj
      · intro hi
        have : oddCode i ∈ oddCode '' A := hprobe.mpr ⟨i, hi, rfl⟩
        obtain ⟨j, hj, hji⟩ := this
        exact (oddCode_injective hji).symm ▸ hj
    letI : Countable targetClass := hcountable.to_subtype
    have hpower : Countable (Set ℕ) := hencode.countable
    exact GenLimit.UnionClosedness.powerSet_not_countable ℕ hpower
  · refine ⟨fun k => 2 ^ k, ?_, 0, ?_⟩
    · exact Nat.pow_right_injective (by norm_num)
    · intro K hK t _
      obtain ⟨A, hA, rfl⟩ := hK
      exact Or.inl ⟨t, rfl⟩
  · intro gen _
    refine ⟨realizedTarget gen, realizedTarget_mem_class gen,
      adversarialPresenter, runTranscript gen, orderedTarget gen, ?_⟩
    exact ⟨rfl, orderedTarget_ambient gen, presentedBy_run gen,
      followsProtocol_run gen, run_clean gen, presentation_injective gen,
      run_complete gen, scored_density_zero gen⟩
