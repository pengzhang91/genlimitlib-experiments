import Stage3Model

open Set
open Stage3Case019

namespace Case019

private def marker (q : ℕ) (z : ℤ) : Prop := ∃ n ≤ q, z = n
private def hasTail (K : Set ℤ) : Prop := ∃ j : ℕ, ∀ n : ℕ, j ≤ n → (n : ℤ) ∈ K
private def hasNegatives (K : Set ℤ) : Prop := ∀ n : ℕ, -(n + 1 : ℤ) ∈ K
private def avoidsMarkers (q : ℕ) (K : Set ℤ) : Prop := ∀ n ≤ q, (n : ℤ) ∉ K

def witnessFamily (q : ℕ) : Set (Set ℤ) :=
  {K | ((∀ z, marker q z → z ∈ K) ∧ hasTail K) ∨
       (hasNegatives K ∧ avoidsMarkers q K)}

private def codedLanguage (q : ℕ) (S : Set ℕ) : Set ℤ :=
  {z | marker q z ∨ (∃ n : ℕ, q + 1 ≤ n ∧ z = n) ∨
    ∃ n ∈ S, z = -(n + 1 : ℤ)}

private theorem codedLanguage_mem (q : ℕ) (S : Set ℕ) :
    codedLanguage q S ∈ witnessFamily q := by
  left
  constructor
  · intro z hz
    exact Or.inl hz
  · refine ⟨q + 1, ?_⟩
    intro n hn
    exact Or.inr (Or.inl ⟨n, hn, rfl⟩)

private theorem codedLanguage_injective (q : ℕ) :
    Function.Injective (codedLanguage q) := by
  intro S T h
  ext n
  have decode (U : Set ℕ) :
      (-(n + 1 : ℤ) ∈ codedLanguage q U) ↔ n ∈ U := by
    constructor
    · rintro (hm | ht | ⟨k, hk, heq⟩)
      · rcases hm with ⟨k, _, heq⟩
        omega
      · rcases ht with ⟨k, _, heq⟩
        omega
      · have : k = n := by omega
        simpa [this] using hk
    · intro hn
      exact Or.inr (Or.inr ⟨n, hn, rfl⟩)
  have pointEq : (-(n + 1 : ℤ) ∈ codedLanguage q S) ↔
      (-(n + 1 : ℤ) ∈ codedLanguage q T) := by rw [h]
  exact (decode S).symm.trans (pointEq.trans (decode T))

private theorem setNat_univ_not_countable :
    ¬(Set.univ : Set (Set ℕ)).Countable := by
  intro h
  let e : ℕ → Set ℕ := Set.enumerateCountable h ∅
  let D : Set ℕ := {n | n ∉ e n}
  have hD : D ∈ (Set.univ : Set (Set ℕ)) := Set.mem_univ D
  obtain ⟨n, hn⟩ := Set.subset_range_enumerate h ∅ hD
  have hmem : n ∈ e n ↔ n ∈ D := Set.ext_iff.mp hn n
  change (n ∈ e n ↔ n ∉ e n) at hmem
  by_cases hp : n ∈ e n
  · exact hmem.mp hp hp
  · exact hp (hmem.mpr hp)

private theorem witnessFamily_not_countable (q : ℕ) :
    ¬(witnessFamily q).Countable := by
  intro h
  have hrange : (Set.range (codedLanguage q)).Countable := h.mono (by
    intro K hK
    rcases hK with ⟨S, rfl⟩
    exact codedLanguage_mem q S)
  have hpre := hrange.preimage (codedLanguage_injective q)
  have : (codedLanguage q ⁻¹' Set.range (codedLanguage q)) = Set.univ := by
    ext S
    simp
  rw [this] at hpre
  exact setNat_univ_not_countable hpre

private theorem witnessFamily_infinite (q : ℕ) :
    ∀ K ∈ witnessFamily q, K.Infinite := by
  intro K hK
  rcases hK with hpos | hneg
  · rcases hpos.2 with ⟨j, hj⟩
    exact Set.infinite_of_injective_forall_mem
      (f := fun n : ℕ => ((j + n : ℕ) : ℤ))
      (by intro a b hab; exact Nat.add_left_cancel (Int.ofNat_inj.mp hab))
      (by intro n; exact hj (j + n) (Nat.le_add_right j n))
  · exact Set.infinite_of_injective_forall_mem
      (f := fun n : ℕ => -(n + 1 : ℤ))
      (by intro a b hab
          have := neg_injective hab
          exact Nat.add_right_cancel (Int.ofNat_inj.mp this))
      hneg.1

theorem witnessFamily_structural (q : ℕ) :
    ¬(witnessFamily q).Countable ∧
      ∀ K ∈ witnessFamily q, K.Infinite :=
  ⟨witnessFamily_not_countable q, witnessFamily_infinite q⟩

end Case019
