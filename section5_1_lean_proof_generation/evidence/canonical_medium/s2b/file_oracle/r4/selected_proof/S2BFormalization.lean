import S2BHelpers

open Set Function

namespace Stage3Work

open Stage3S2B

 theorem targetClass_uncountable : ¬ targetClass.Countable := by
  intro hcount
  classical
  have hcore : core ∈ targetClass := by
    refine ⟨∅, Set.empty_subset ordinary, ?_⟩
    simp
  letI : Nonempty targetClass := ⟨⟨core, hcore⟩⟩
  letI : Countable targetClass := hcount
  obtain ⟨f, hf⟩ := exists_surjective_nat targetClass
  let A : Language := {z | ∃ n : ℕ, z = 2*n+3 ∧ z ∉ (f n : Language)}
  let D : Language := core ∪ A
  have hA : A ⊆ ordinary := by
    intro z hz
    rcases hz with ⟨n, rfl, hn⟩
    exact oddThree_not_core n
  have hD : D ∈ targetClass := ⟨A, hA, rfl⟩
  obtain ⟨n, hn⟩ := hf ⟨D, hD⟩
  have hsets : (f n : Language) = D := congrArg Subtype.val hn
  by_cases hmem : 2*n+3 ∈ (f n : Language)
  · have hmemD := hmem
    rw [hsets] at hmemD
    rcases hmemD with hcoremem | hAmem
    · exact oddThree_not_core n hcoremem
    · rcases hAmem with ⟨m, hmval, hmnot⟩
      have hmn : m = n := by omega
      subst m
      exact hmnot hmem
  · have hAmem : 2*n+3 ∈ A := ⟨n, rfl, hmem⟩
    apply hmem
    rw [hsets]
    exact Or.inr hAmem

 theorem uniformlyGeneratable : UniformlyGeneratableWithoutSamples := by
  refine ⟨fun t => 2^t, ?_, 0, ?_⟩
  · exact Nat.pow_right_injective (by omega)
  · intro K hK t ht
    rcases hK with ⟨A, hA, rfl⟩
    exact Or.inl ⟨t, rfl⟩

 theorem negativeClaim : NegativeClaim := by
  intro gen hgen
  refine ⟨K gen, K_targetClass gen, presenter gen, tr gen, orderedK gen, ?_⟩
  exact ⟨rfl, orderedK_strict gen, presentedBy gen, followsProtocol gen,
    clean gen, presentation_injective gen, complete gen, scored_upperDensity_zero gen⟩

end Stage3Work

open Stage3S2B

theorem stage3_result : Stage3S2B.MainClaim := by
  exact ⟨Stage3Work.targetClass_uncountable, Stage3Work.uniformlyGeneratable,
    Stage3Work.negativeClaim⟩
