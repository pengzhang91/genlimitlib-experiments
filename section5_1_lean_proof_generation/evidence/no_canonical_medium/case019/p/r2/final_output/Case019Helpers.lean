import Stage3Model

open Set

namespace Case019Partial

def markers (q : ℕ) : Set ℤ := {z | 0 ≤ z ∧ z ≤ (q : ℤ)}

def positiveTail (j : ℕ) : Set ℤ := {z | (j : ℤ) ≤ z}

def negativeHalf : Set ℤ := {z | z < 0}

def hierarchyFamily (q : ℕ) : Set (Set ℤ) :=
  {K | (∃ j : ℕ, ∃ A : Set ℤ, K = markers q ∪ A ∪ positiveTail j) ∨
       (∃ A : Set ℤ, Disjoint A (markers q) ∧ K = A ∪ negativeHalf)}

def codedLanguage (B : Set ℕ) : Set ℤ :=
  {z | 0 ≤ z ∨ ∃ n ∈ B, z = -((n : ℤ) + 1)}

theorem codedLanguage_mem (q : ℕ) (B : Set ℕ) :
    codedLanguage B ∈ hierarchyFamily q := by
  left
  refine ⟨0, codedLanguage B, ?_⟩
  apply Set.Subset.antisymm
  · intro z hz
    exact Or.inl (Or.inr hz)
  · intro z hz
    rcases hz with (⟨hm, _⟩ | hz) | ht
    · exact Or.inl hm
    · exact hz
    · exact Or.inl ht

theorem codedLanguage_injective : Function.Injective codedLanguage := by
  intro A B h
  ext n
  have key (C : Set ℕ) :
      -((n : ℤ) + 1) ∈ codedLanguage C ↔ n ∈ C := by
    constructor
    · rintro (hneg | ⟨m, hm, heq⟩)
      · omega
      · have hmn : m = n := by omega
        simpa [hmn] using hm
    · intro hn
      exact Or.inr ⟨n, hn, rfl⟩
  rw [← key A, h, key B]

theorem setNat_univ_not_countable :
    ¬(Set.univ : Set (Set ℕ)).Countable := by
  intro hcount
  let enum : ℕ → Set ℕ := Set.enumerateCountable hcount ∅
  have hrange : Set.range enum = Set.univ := by
    exact Set.range_enumerateCountable_of_mem hcount (Set.mem_univ ∅)
  let diagonal : Set ℕ := {n | n ∉ enum n}
  obtain ⟨k, hk⟩ : diagonal ∈ Set.range enum := by
    rw [hrange]
    exact Set.mem_univ diagonal
  have hdiag : k ∈ diagonal ↔ k ∉ enum k := Iff.rfl
  have hself : k ∈ diagonal ↔ k ∉ diagonal := by simpa [hk] using hdiag
  by_cases hkd : k ∈ diagonal
  · exact (hself.mp hkd) hkd
  · exact hkd (hself.mpr hkd)

theorem hierarchyFamily_uncountable (q : ℕ) :
    ¬(hierarchyFamily q).Countable := by
  intro hcount
  have hrange : (Set.range codedLanguage).Countable :=
    hcount.mono (by
      rintro K ⟨B, rfl⟩
      exact codedLanguage_mem q B)
  have hpreimage : (codedLanguage ⁻¹' Set.range codedLanguage).Countable :=
    hrange.preimage codedLanguage_injective
  have hdomain : (Set.univ : Set (Set ℕ)).Countable := by
    simpa only [preimage_range] using hpreimage
  exact setNat_univ_not_countable hdomain

theorem hierarchyFamily_infinite (q : ℕ) (K : Set ℤ)
    (hK : K ∈ hierarchyFamily q) : K.Infinite := by
  rcases hK with ⟨j, A, rfl⟩ | ⟨A, hA, rfl⟩
  · have hinj : Function.Injective (fun n : ℕ => ((j + n : ℕ) : ℤ)) := by
      intro m n h
      exact Nat.add_left_cancel (Int.ofNat_inj.mp h)
    apply (Set.infinite_range_of_injective hinj).mono
    rintro z ⟨n, rfl⟩
    exact Or.inr (by simp [positiveTail])
  · have hinj : Function.Injective (fun n : ℕ => -((n : ℤ) + 1)) := by
      intro m n h
      have hsum : (m : ℤ) + 1 = (n : ℤ) + 1 := neg_inj.mp h
      have hmn : (m : ℤ) = (n : ℤ) := add_right_cancel hsum
      exact Int.ofNat_inj.mp hmn
    apply (Set.infinite_range_of_injective hinj).mono
    rintro z ⟨n, rfl⟩
    exact Or.inr (by
      change -((n : ℤ) + 1) < 0
      omega)

end Case019Partial
