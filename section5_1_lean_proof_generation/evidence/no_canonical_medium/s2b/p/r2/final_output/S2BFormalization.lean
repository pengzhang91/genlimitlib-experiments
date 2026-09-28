import Stage3Model
import Mathlib.Data.Set.Countable

open Set

namespace Stage3Work

open Stage3S2B

lemma pow_two_in_core (k : ℕ) : 2 ^ k ∈ core := ⟨k, rfl⟩

lemma pow_two_injective : Function.Injective (fun k : ℕ => 2 ^ k) :=
  Nat.pow_right_injective (by omega)

lemma uniform : UniformlyGeneratableWithoutSamples := by
  refine ⟨fun k => 2 ^ k, pow_two_injective, 0, ?_⟩
  intro K hK t _
  rcases hK with ⟨A, hA, rfl⟩
  exact Or.inl (pow_two_in_core t)

lemma odd_ge_three_ordinary (n : ℕ) : 2 * n + 3 ∈ ordinary := by
  simp only [ordinary, Set.mem_compl_iff, core, Set.mem_range]
  rintro ⟨k, hk⟩
  cases k with
  | zero => omega
  | succ k =>
      have heven : Even (2 ^ (k + 1)) := ⟨2 ^ k, by ring⟩
      have hodd : Odd (2 * n + 3) := ⟨n + 1, by omega⟩
      rw [hk] at heven
      rcases heven with ⟨a, ha⟩
      rcases hodd with ⟨b, hb⟩
      omega

lemma ordinary_infinite : ordinary.Infinite := by
  let f : ℕ → ℕ := fun n => 2 * n + 3
  have hf : Function.Injective f := by
    intro a b h
    dsimp [f] at h
    omega
  have hr : Set.range f ⊆ ordinary := by
    rintro z ⟨n, rfl⟩
    exact odd_ge_three_ordinary n
  exact (Set.infinite_range_of_injective hf).mono hr

lemma targetClass_uncountable : ¬ targetClass.Countable := by
  intro hcount
  let embed : Set ordinary → Language := fun A => core ∪ ((↑) '' A)
  have hembed_mem : ∀ A : Set ordinary, embed A ∈ targetClass := by
    intro A
    refine ⟨(↑) '' A, ?_, rfl⟩
    rintro z ⟨a, ha, rfl⟩
    exact a.property
  have hinj : Function.Injective embed := by
    intro A B hAB
    ext a
    have haOrd : (a : ℕ) ∉ core := a.property
    have hmem (C : Set ordinary) : (a : ℕ) ∈ embed C ↔ a ∈ C := by
      simp [embed, haOrd]
    rw [← hmem A, hAB, hmem B]
  have hrange : (Set.range embed).Countable := by
    apply hcount.mono
    rintro K ⟨A, rfl⟩
    exact hembed_mem A
  have hdomain : (Set.univ : Set (Set ordinary)).Countable := by
    have hp := hrange.preimage hinj
    simpa using hp
  rw [Set.countable_iff_exists_surjective (s := (Set.univ : Set (Set ordinary)))
    Set.univ_nonempty] at hdomain
  rcases hdomain with ⟨enum0, henum0⟩
  let enum : ℕ → Set ordinary := fun n => (enum0 n).1
  have henum : Function.Surjective enum := by
    intro A
    obtain ⟨n, hn⟩ := henum0 ⟨A, Set.mem_univ A⟩
    exact ⟨n, congrArg Subtype.val hn⟩
  let f : ℕ → ordinary := fun n => ⟨2 * n + 3, odd_ge_three_ordinary n⟩
  have hf : Function.Injective f := by
    intro a b h
    have hv := congrArg Subtype.val h
    dsimp [f] at hv
    omega
  let diagonal : Set ordinary := {a | ∃ n, f n = a ∧ a ∉ enum n}
  obtain ⟨m, hm⟩ := henum diagonal
  have hdiag : f m ∈ diagonal ↔ f m ∉ diagonal := by
    constructor
    · rintro ⟨n, hn, hnot⟩
      have : n = m := hf hn
      subst n
      simpa [hm] using hnot
    · intro hnot
      exact ⟨m, rfl, by simpa [hm] using hnot⟩
  by_cases h : f m ∈ diagonal
  · exact (hdiag.mp h) h
  · exact h (hdiag.mpr h)

end Stage3Work

theorem stage3_result : Stage3S2B.MainClaim := by
  refine ⟨Stage3Work.targetClass_uncountable, Stage3Work.uniform, ?_⟩
  sorry
