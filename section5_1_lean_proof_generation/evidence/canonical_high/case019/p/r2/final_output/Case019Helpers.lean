import Stage3Model

open Set Function
open Stage3Case019

namespace Case019Formalization

def markers (q : ℕ) : Set ℤ := {z | 0 ≤ z ∧ z ≤ (q : ℤ)}

def positiveTail (j : ℕ) : Set ℤ := {z | (j : ℤ) ≤ z}

def negatives : Set ℤ := {z | z < 0}

def upperFamily (q : ℕ) (K : Set ℤ) : Prop :=
  markers q ⊆ K ∧ ∃ j : ℕ, positiveTail j ⊆ K

def lowerFamily (q : ℕ) (K : Set ℤ) : Prop :=
  negatives ⊆ K ∧ Disjoint (markers q) K

def separationFamily (q : ℕ) : LanguageClass ℤ :=
  {K | upperFamily q K ∨ lowerFamily q K}

def negCode (n : ℕ) : ℤ := -((n : ℤ) + 1)

def codedLanguage (q : ℕ) (S : Set ℕ) : Set ℤ :=
  {z | z ∈ markers q ∨ z ∈ positiveTail (q + 1) ∨ ∃ n ∈ S, negCode n = z}

lemma negCode_negative (n : ℕ) : negCode n < 0 := by
  have hn : (0 : ℤ) ≤ (n : ℤ) := Int.natCast_nonneg n
  dsimp [negCode]
  omega

lemma negCode_injective : Function.Injective negCode := by
  intro m n h
  simp [negCode] at h
  exact h

lemma negCode_not_marker (q n : ℕ) : negCode n ∉ markers q := by
  intro h
  exact (not_lt_of_ge h.1) (negCode_negative n)

lemma negCode_not_tail (q n : ℕ) : negCode n ∉ positiveTail (q + 1) := by
  intro h
  have hnonneg : (0 : ℤ) ≤ ((q + 1 : ℕ) : ℤ) := Int.natCast_nonneg (q + 1)
  have hzero : (0 : ℤ) ≤ negCode n := hnonneg.trans h
  exact (not_lt_of_ge hzero) (negCode_negative n)

lemma codedLanguage_mem (q : ℕ) (S : Set ℕ) :
    codedLanguage q S ∈ separationFamily q := by
  left
  refine ⟨?_, q + 1, ?_⟩ <;> intro z hz
  · exact Or.inl hz
  · exact Or.inr (Or.inl hz)

lemma negCode_mem_codedLanguage_iff (q : ℕ) (S : Set ℕ) (n : ℕ) :
    negCode n ∈ codedLanguage q S ↔ n ∈ S := by
  constructor
  · intro hn
    rcases hn with hn | hn | ⟨m, hm, hmn⟩
    · exact (negCode_not_marker q n hn).elim
    · exact (negCode_not_tail q n hn).elim
    · exact negCode_injective hmn ▸ hm
  · intro hn
    exact Or.inr (Or.inr ⟨n, hn, rfl⟩)

lemma codedLanguage_injective (q : ℕ) : Function.Injective (codedLanguage q) := by
  intro S T h
  ext n
  rw [← negCode_mem_codedLanguage_iff q S n,
    h, negCode_mem_codedLanguage_iff q T n]

lemma separationFamily_nonempty (q : ℕ) : (separationFamily q).Nonempty := by
  exact ⟨codedLanguage q ∅, codedLanguage_mem q ∅⟩

lemma separationFamily_not_countable (q : ℕ) : ¬(separationFamily q).Countable := by
  intro hcount
  obtain ⟨enumerate, henumerate⟩ := hcount.exists_surjective (separationFamily_nonempty q)
  let diagonal : Set ℕ := {n | negCode n ∉ (enumerate n : Set ℤ)}
  let K := codedLanguage q diagonal
  have hK : K ∈ separationFamily q := codedLanguage_mem q diagonal
  obtain ⟨n, hn⟩ := henumerate ⟨K, hK⟩
  have hEq : (enumerate n : Set ℤ) = K := congrArg Subtype.val hn
  have hdiag : negCode n ∈ K ↔ n ∈ diagonal := by
    exact negCode_mem_codedLanguage_iff q diagonal n
  have hcontra : negCode n ∈ (enumerate n : Set ℤ) ↔ negCode n ∉ (enumerate n : Set ℤ) := by
    constructor
    · intro hmem
      have hk : negCode n ∈ K := by simpa [hEq] using hmem
      have hd : n ∈ diagonal := hdiag.mp hk
      change negCode n ∉ (enumerate n : Set ℤ) at hd
      exact hd
    · intro hnot
      have hd : n ∈ diagonal := by
        change negCode n ∉ (enumerate n : Set ℤ)
        exact hnot
      have hk : negCode n ∈ K := hdiag.mpr hd
      simpa [hEq] using hk
  by_cases hz : negCode n ∈ (enumerate n : Set ℤ)
  · exact (hcontra.mp hz) hz
  · exact hz (hcontra.mpr hz)

lemma upperFamily_infinite {q : ℕ} {K : Set ℤ} (hK : upperFamily q K) : K.Infinite := by
  obtain ⟨j, hj⟩ := hK.2
  exact (Set.Ici_infinite (j : ℤ)).mono hj

lemma lowerFamily_infinite {q : ℕ} {K : Set ℤ} (hK : lowerFamily q K) : K.Infinite := by
  have hneg : (Set.Iic (-1 : ℤ)).Infinite := Set.Iic_infinite (-1 : ℤ)
  apply hneg.mono
  intro z hz
  apply hK.1
  change z < 0
  change z ≤ -1 at hz
  omega

lemma separationFamily_infinite (q : ℕ) :
    ∀ K ∈ separationFamily q, K.Infinite := by
  intro K hK
  rcases hK with hK | hK
  · exact upperFamily_infinite hK
  · exact lowerFamily_infinite hK

end Case019Formalization
