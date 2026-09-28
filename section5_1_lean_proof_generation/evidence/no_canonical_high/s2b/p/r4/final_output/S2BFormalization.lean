import Stage3Model

open Set Filter
open scoped Topology

namespace Stage3Work

open Stage3S2B

def code (n : ℕ) : ℕ := 2 * n + 3

lemma code_injective : Function.Injective code := by
  intro a b h
  simp [code] at h
  omega

lemma code_not_core (n : ℕ) : code n ∉ core := by
  rintro ⟨k, hk⟩
  rcases k with _ | k
  · simp [code] at hk
  · have he : Even (2 ^ (k + 1)) := (Nat.even_pow).2 ⟨by decide, by omega⟩
    have ho : ¬ Even (code n) := by
      rw [Nat.not_even_iff_odd]
      exact ⟨n + 1, by simp [code, Nat.mul_comm]; omega⟩
    apply ho
    rwa [← hk]

lemma code_mem_ordinary (n : ℕ) : code n ∈ ordinary := by
  simpa [ordinary] using code_not_core n

def embedTarget (A : Language) : Language := core ∪ code '' A

lemma embedTarget_mem (A : Language) : embedTarget A ∈ targetClass := by
  refine ⟨code '' A, ?_, rfl⟩
  intro z hz
  rcases hz with ⟨n, hn, rfl⟩
  exact code_mem_ordinary n

lemma embedTarget_injective : Function.Injective embedTarget := by
  intro A B h
  ext n
  have hcode := Set.ext_iff.mp h (code n)
  simp only [embedTarget, mem_union, mem_image] at hcode
  simp only [code_not_core n, false_or] at hcode
  constructor
  · intro hn
    have : code n ∈ code '' B := hcode.mp ⟨n, hn, rfl⟩
    rcases this with ⟨m, hm, heq⟩
    exact (code_injective heq).symm ▸ hm
  · intro hn
    have : code n ∈ code '' A := hcode.mpr ⟨n, hn, rfl⟩
    rcases this with ⟨m, hm, heq⟩
    exact (code_injective heq).symm ▸ hm

lemma targetClass_not_countable : ¬ targetClass.Countable := by
  intro hc
  have himage : (embedTarget '' (Set.univ : Set Language)).Countable :=
    hc.mono (by
      intro K hK
      rcases hK with ⟨A, -, rfl⟩
      exact embedTarget_mem A)
  have huniv : (Set.univ : Set Language).Countable :=
    Set.countable_of_injective_of_countable_image embedTarget_injective.injOn himage
  rcases Set.countable_iff_exists_subset_range.mp huniv with ⟨f, hf⟩
  let diagonal : Language := {n | n ∉ f n}
  rcases hf (Set.mem_univ diagonal) with ⟨k, hk⟩
  have hdiag : diagonal k ↔ f k k := by rw [← hk]
  change (k ∉ f k) ↔ k ∈ f k at hdiag
  exact not_iff_self hdiag

lemma core_generator : UniformlyGeneratableWithoutSamples := by
  refine ⟨fun n => 2 ^ n, Nat.pow_right_injective (by decide), 0, ?_⟩
  intro K hK t ht
  rcases hK with ⟨A, hA, rfl⟩
  exact Or.inl ⟨t, rfl⟩

end Stage3Work

open Stage3Work

/-- Checked unconditional portion of `Stage3S2B.MainClaim`. -/
theorem stage3_unconditional :
    ¬ Stage3S2B.targetClass.Countable ∧
      Stage3S2B.UniformlyGeneratableWithoutSamples := by
  exact ⟨targetClass_not_countable, core_generator⟩
