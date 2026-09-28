import Stage3Model
import Mathlib.SetTheory.Cardinal.Continuum

open Set Filter

namespace Stage3Work

open Stage3S2B

private def code (n : ℕ) : ℕ := 2 * n + 3

private theorem code_injective : Function.Injective code := by
  intro a b h
  simp [code] at h
  omega

private theorem code_not_core (n : ℕ) : code n ∉ core := by
  rintro ⟨k, hk⟩
  by_cases h0 : k = 0
  · subst k
    simp [code] at hk
  · have he : Even (2 ^ k) := (Nat.even_pow.mpr ⟨by simp, h0⟩)
    have ho : Odd (code n) := by
      refine ⟨n + 1, ?_⟩
      simp [code]
      omega
    have hne : ¬ Even (code n) := Nat.not_even_iff_odd.mpr ho
    exact hne (hk ▸ he)

private def family (A : Set ℕ) : Language := core ∪ code '' A

private theorem family_mem (A : Set ℕ) : family A ∈ targetClass := by
  refine ⟨code '' A, ?_, rfl⟩
  intro z hz
  rcases hz with ⟨n, hn, rfl⟩
  exact code_not_core n

private theorem family_injective : Function.Injective family := by
  intro A B h
  ext n
  have hcA : code n ∈ family A ↔ n ∈ A := by
    simp only [family, mem_union, mem_image]
    constructor
    · rintro (hc | ⟨m, hm, heq⟩)
      · exact False.elim (code_not_core n hc)
      · exact (code_injective heq).symm ▸ hm
    · intro hn
      exact Or.inr ⟨n, hn, rfl⟩
  have hcB : code n ∈ family B ↔ n ∈ B := by
    simp only [family, mem_union, mem_image]
    constructor
    · rintro (hc | ⟨m, hm, heq⟩)
      · exact False.elim (code_not_core n hc)
      · exact (code_injective heq).symm ▸ hm
    · intro hn
      exact Or.inr ⟨n, hn, rfl⟩
  rw [← hcA, ← hcB, h]

 theorem targetClass_not_countable : ¬ targetClass.Countable := by
  intro hcount
  have himage : (family '' (Set.univ : Set (Set ℕ))).Countable := by
    apply hcount.mono
    rintro K ⟨A, -, rfl⟩
    exact family_mem A
  have huniv : (Set.univ : Set (Set ℕ)).Countable :=
    Set.countable_of_injective_of_countable_image
      (fun _ _ _ _ hab => family_injective hab) himage
  have hsurj : ∃ f : ℕ → (Set.univ : Set (Set ℕ)), Function.Surjective f :=
    (Set.countable_iff_exists_surjective (s := (Set.univ : Set (Set ℕ)))
      Set.univ_nonempty).mp huniv
  rcases hsurj with ⟨f, hf⟩
  let diagonal : Set ℕ := {n | n ∉ (f n : Set ℕ)}
  rcases hf ⟨diagonal, Set.mem_univ diagonal⟩ with ⟨n, hn⟩
  have hdiag : n ∈ diagonal ↔ n ∉ (f n : Set ℕ) := Iff.rfl
  have heq : (f n : Set ℕ) = diagonal := congrArg Subtype.val hn
  rw [heq] at hdiag
  exact iff_not_self hdiag

 theorem uniform_generation : UniformlyGeneratableWithoutSamples := by
  refine ⟨fun t => 2 ^ t, Nat.pow_right_injective (by decide), 0, ?_⟩
  intro K hK t ht
  rcases hK with ⟨A, hA, rfl⟩
  exact Or.inl ⟨t, rfl⟩

end Stage3Work
