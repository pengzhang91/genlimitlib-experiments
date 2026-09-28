import DensityScratch

open Set Filter
open scoped Topology BigOperators

namespace Stage3Proof

open Stage3S2B

lemma odd_three_not_core (n : ℕ) : 2 * n + 3 ∉ core := by
  rintro ⟨k, hk⟩
  cases k with
  | zero => simp at hk
  | succ k =>
      have heven : Even (2 ^ (k + 1)) := by
        exact ⟨2 ^ k, by rw [pow_succ]; omega⟩
      have hodd : Odd (2 * n + 3) := by
        exact ⟨n + 1, by omega⟩
      exact (Nat.not_even_iff_odd.mpr hodd) (hk ▸ heven)

lemma targetClass_uncountable : ¬ targetClass.Countable := by
  let e : ℕ → ℕ := fun n => 2 * n + 3
  let F : Set ℕ → Language := fun A => core ∪ e '' A
  have he : Function.Injective e := by
    intro a b h
    dsimp [e] at h
    omega
  have heOrd : ∀ n, e n ∈ ordinary := by
    intro n
    exact odd_three_not_core n
  have hF : Function.Injective F := by
    intro A B hAB
    ext n
    constructor
    · intro hn
      have : e n ∈ F A := by exact Or.inr ⟨n, hn, rfl⟩
      rw [hAB] at this
      rcases this with hcore | ⟨m, hm, hem⟩
      · exact False.elim (heOrd n hcore)
      · exact he hem.symm ▸ hm
    · intro hn
      have : e n ∈ F B := by exact Or.inr ⟨n, hn, rfl⟩
      rw [← hAB] at this
      rcases this with hcore | ⟨m, hm, hem⟩
      · exact False.elim (heOrd n hcore)
      · exact he hem.symm ▸ hm
  intro hcount
  have hrange : (Set.range F).Countable := hcount.mono (by
    rintro K ⟨A, rfl⟩
    exact ⟨e '' A, by
      refine ⟨?_, rfl⟩
      intro z hz
      rcases hz with ⟨n, -, rfl⟩
      exact heOrd n⟩)
  have huniv : (Set.univ : Set (Set ℕ)).Countable := by
    have hp := hrange.preimage hF
    simpa using hp
  rcases huniv.exists_surjective Set.univ_nonempty with ⟨f, hf⟩
  let D : Set ℕ := {n | n ∉ (f n : Set ℕ)}
  obtain ⟨n, hn⟩ := hf ⟨D, Set.mem_univ D⟩
  have hdiag := congrArg (fun A : Set ℕ => n ∈ A) (congrArg Subtype.val hn)
  simp [D] at hdiag

lemma uniform_generation : UniformlyGeneratableWithoutSamples := by
  refine ⟨fun k => 2 ^ k, pow_two_injective, 0, ?_⟩
  intro K hK t ht
  rcases hK with ⟨A, hA, rfl⟩
  exact Or.inl ⟨t, rfl⟩

end Stage3Proof

open Stage3Proof

theorem stage3_result : Stage3S2B.MainClaim := by
  refine ⟨targetClass_uncountable, uniform_generation, ?_⟩
  intro gen hgen
  refine ⟨realizedTarget gen, ?_, diagonalPresenter, interactionTranscript gen,
    orderedTarget gen, ?_⟩
  · exact target_mem_class gen
  · refine ⟨rfl, orderedTarget_strictMono gen, transcript_presented gen,
      ?_, target_clean gen, presentation_injective gen, target_complete gen, ?_⟩
    · exact interaction_follows_protocol gen
    · exact scored_upperDensity_zero gen
