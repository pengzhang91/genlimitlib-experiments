import Greedy

open Set
open Stage3Case019

namespace Case019

def posLine (n : ℕ) : ℤ := Int.ofNat n

def negLine (n : ℕ) : ℤ := -Int.ofNat (n + 1)

theorem posLine_injective : Function.Injective posLine := by
  intro a b h
  exact Int.ofNat_inj.mp h

theorem negLine_injective : Function.Injective negLine := by
  intro a b h
  change -Int.ofNat (a + 1) = -Int.ofNat (b + 1) at h
  have hab : a + 1 = b + 1 := Int.ofNat_inj.mp (neg_inj.mp h)
  omega

theorem negLine_not_posLine (a b : ℕ) : negLine a ≠ posLine b := by
  have hn : negLine a < 0 := by
    change -Int.ofNat (a + 1) < 0
    exact neg_neg_of_pos (Int.ofNat_pos.mpr (by omega))
  have hp : 0 ≤ posLine b := by simp [posLine]
  omega

/-- A simple uncountable family sharing the nonnegative integer half-line. -/
def commonHalfFamily : LanguageClass ℤ :=
  {K | Set.range posLine ⊆ K}

/-- Embed every subset of `ℕ` by freely choosing negative points. -/
def encodeSubset (S : Set ℕ) : Stage3Case019.Language ℤ :=
  Set.range posLine ∪ negLine '' S

theorem encodeSubset_mem (S : Set ℕ) : encodeSubset S ∈ commonHalfFamily := by
  exact Set.subset_union_left

theorem encodeSubset_injective : Function.Injective encodeSubset := by
  intro S T hST
  ext n
  have hmem : negLine n ∈ encodeSubset S ↔ n ∈ S := by
    constructor
    · intro hn
      rcases hn with hn | hn
      · obtain ⟨m, hm⟩ := hn
        exact False.elim (negLine_not_posLine n m hm.symm)
      · obtain ⟨m, hm, hmn⟩ := hn
        have : m = n := negLine_injective hmn
        simpa [this] using hm
    · intro hn
      exact Or.inr ⟨n, hn, rfl⟩
  have hmemT : negLine n ∈ encodeSubset T ↔ n ∈ T := by
    constructor
    · intro hn
      rcases hn with hn | hn
      · obtain ⟨m, hm⟩ := hn
        exact False.elim (negLine_not_posLine n m hm.symm)
      · obtain ⟨m, hm, hmn⟩ := hn
        have : m = n := negLine_injective hmn
        simpa [this] using hm
    · intro hn
      exact Or.inr ⟨n, hn, rfl⟩
  rw [← hmem, ← hmemT, hST]

theorem commonHalfFamily_uncountable : ¬commonHalfFamily.Countable := by
  intro hcount
  have hrange : (Set.range encodeSubset).Countable :=
    hcount.mono (by
      intro K hK
      obtain ⟨S, rfl⟩ := hK
      exact encodeSubset_mem S)
  have hpre : (encodeSubset ⁻¹' Set.range encodeSubset).Countable :=
    hrange.preimage encodeSubset_injective
  have heq : encodeSubset ⁻¹' Set.range encodeSubset = (Set.univ : Set (Set ℕ)) := by
    ext S
    simp
  have huniv : (Set.univ : Set (Set ℕ)).Countable := heq ▸ hpre
  obtain ⟨f, hf⟩ := Set.countable_iff_exists_subset_range.mp huniv
  let diagonal : Set ℕ := {n | n ∉ f n}
  obtain ⟨k, hk⟩ := hf (Set.mem_univ diagonal)
  have hdiag : k ∈ diagonal ↔ k ∉ diagonal := by
    change (k ∉ f k) ↔ k ∉ diagonal
    rw [hk]
  tauto

theorem commonHalfFamily_infinite (K : Stage3Case019.Language ℤ)
    (hK : K ∈ commonHalfFamily) : K.Infinite := by
  exact ((Set.infinite_range_iff posLine_injective).2 inferInstance).mono hK

/-- One semantic generator is novel and valid on every stream for every target
in the common-half-line family; no presentation assumption is needed. -/
theorem commonHalfFamily_uniform_novelty :
    ∃ gen : Generator ℤ,
      ∀ K ∈ commonHalfFamily, ∀ input : Stream ℤ,
        NovelGeneratesAfterInput input (outputAfterInput gen input) K := by
  refine ⟨greedyGenerator posLine posLine_injective, ?_⟩
  intro K hK input
  exact greedy_novel_after_input posLine posLine_injective input K hK

end Case019
