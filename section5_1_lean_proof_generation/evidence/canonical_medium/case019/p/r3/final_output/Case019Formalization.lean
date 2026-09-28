import Stage3Model

open Set
open Stage3Case019

namespace Case019Work

/-- The finite marker block used by the adjacent-level witness. -/
def markers (q : ℕ) : Set ℤ := {z | 0 ≤ z ∧ z ≤ (q : ℤ)}

/-- The nonnegative tail beginning at `j`. -/
def positiveTail (j : ℕ) : Set ℤ := {z | (j : ℤ) ≤ z}

/-- The negative half-line. -/
def negativeHalf : Set ℤ := {z | z < 0}

/-- Languages containing the marker block and some nonnegative tail. -/
def upperLanguages (q : ℕ) : Set (Set ℤ) :=
  {K | markers q ⊆ K ∧ ∃ j : ℕ, positiveTail j ⊆ K}

/-- Languages containing the negative half-line and omitting every marker. -/
def lowerLanguages (q : ℕ) : Set (Set ℤ) :=
  {K | negativeHalf ⊆ K ∧ Disjoint K (markers q)}

/-- The extensional marker-and-tail witness class from the supplied proof. -/
def witnessFamily (q : ℕ) : LanguageClass ℤ := upperLanguages q ∪ lowerLanguages q

lemma positiveTail_infinite (j : ℕ) : (positiveTail j).Infinite := by
  have hinj : Function.Injective (fun n : ℕ => ((j + n : ℕ) : ℤ)) := by
    intro a b h
    change ((j + a : ℕ) : ℤ) = ((j + b : ℕ) : ℤ) at h
    have hab : j + a = j + b := Int.ofNat_inj.mp h
    exact Nat.add_left_cancel hab
  have hrange := Set.infinite_range_of_injective hinj
  apply hrange.mono
  rintro z ⟨n, rfl⟩
  simp [positiveTail]

lemma negativeHalf_infinite : negativeHalf.Infinite := by
  have hinj : Function.Injective (fun n : ℕ => -((n : ℤ) + 1)) := by
    intro a b h
    dsimp at h
    have hab : (a : ℤ) = (b : ℤ) := by omega
    exact_mod_cast hab
  have hrange := Set.infinite_range_of_injective hinj
  apply hrange.mono
  rintro z ⟨n, rfl⟩
  change -((n : ℤ) + 1) < 0
  omega

lemma witnessFamily_infinite (q : ℕ) :
    ∀ K ∈ witnessFamily q, K.Infinite := by
  intro K hK
  rcases hK with hK | hK
  · rcases hK.2 with ⟨j, hj⟩
    exact (positiveTail_infinite j).mono hj
  · exact negativeHalf_infinite.mono hK.1

/-- Encode an arbitrary set of naturals into the freely chosen negative part
of an upper-family language. -/
def encodeLanguage (q : ℕ) (S : Set ℕ) : Set ℤ :=
  markers q ∪ positiveTail (q + 1) ∪
    {z | ∃ n ∈ S, z = -((n : ℤ) + 1)}

lemma encodeLanguage_mem (q : ℕ) (S : Set ℕ) :
    encodeLanguage q S ∈ witnessFamily q := by
  left
  constructor
  · intro z hz
    exact Or.inl (Or.inl hz)
  · exact ⟨q + 1, fun z hz => Or.inl (Or.inr hz)⟩

lemma encodeLanguage_injective (q : ℕ) : Function.Injective (encodeLanguage q) := by
  intro S T h
  ext n
  let z : ℤ := -((n : ℤ) + 1)
  have hzneg : z < 0 := by dsimp [z]; omega
  have hznotmarkers : z ∉ markers q := by
    intro hz
    exact (not_lt_of_ge hz.1) hzneg
  have hznottail : z ∉ positiveTail (q + 1) := by
    intro hz
    have : (0 : ℤ) ≤ z := le_trans (by omega) hz
    omega
  have hS : z ∈ encodeLanguage q S ↔ n ∈ S := by
    simp only [encodeLanguage, mem_union, mem_setOf_eq]
    constructor
    · intro hz
      rcases hz with (hz | hz) | ⟨m, hm, heq⟩
      · exact False.elim (hznotmarkers hz)
      · exact False.elim (hznottail hz)
      · have : (m : ℤ) = (n : ℤ) := by omega
        have : m = n := by exact_mod_cast this
        simpa [this] using hm
    · intro hn
      exact Or.inr ⟨n, hn, rfl⟩
  have hT : z ∈ encodeLanguage q T ↔ n ∈ T := by
    simp only [encodeLanguage, mem_union, mem_setOf_eq]
    constructor
    · intro hz
      rcases hz with (hz | hz) | ⟨m, hm, heq⟩
      · exact False.elim (hznotmarkers hz)
      · exact False.elim (hznottail hz)
      · have : (m : ℤ) = (n : ℤ) := by omega
        have : m = n := by exact_mod_cast this
        simpa [this] using hm
    · intro hn
      exact Or.inr ⟨n, hn, rfl⟩
  rw [← hS, h, hT]

lemma witnessFamily_uncountable (q : ℕ) : ¬(witnessFamily q).Countable := by
  intro hcount
  have hrange : (Set.range (encodeLanguage q)).Countable := by
    apply Set.Countable.mono
    · rintro K ⟨S, rfl⟩
      exact encodeLanguage_mem q S
    · exact hcount
  have hpre := hrange.preimage (encodeLanguage_injective q)
  have huniv : (Set.univ : Set (Set ℕ)).Countable := by
    simpa using hpre
  have hnonempty : (Set.univ : Set (Set ℕ)).Nonempty := ⟨∅, trivial⟩
  rcases (Set.countable_iff_exists_surjective hnonempty).1 huniv with ⟨f, hf⟩
  let diagonal : Set ℕ := {n | n ∉ (f n : Set ℕ)}
  rcases hf ⟨diagonal, trivial⟩ with ⟨n, hn⟩
  have hn' : (f n : Set ℕ) = diagonal := congrArg Subtype.val hn
  have hdiag : n ∈ diagonal ↔ n ∉ diagonal := by
    constructor
    · intro hd
      have hnot : n ∉ (f n : Set ℕ) := by
        simpa only [diagonal, Set.mem_setOf_eq] using hd
      simpa only [hn'] using hnot
    · intro hnot
      have hnot' : n ∉ (f n : Set ℕ) := by
        simpa only [hn'] using hnot
      simpa only [diagonal, Set.mem_setOf_eq] using hnot'
  by_cases hmem : n ∈ diagonal
  · exact (hdiag.mp hmem) hmem
  · exact hmem (hdiag.mpr hmem)

/-- Checked structural core of the uncountable witness. -/
theorem witnessFamily_structure (q : ℕ) :
    ¬(witnessFamily q).Countable ∧
      ∀ K ∈ witnessFamily q, K.Infinite :=
  ⟨witnessFamily_uncountable q, witnessFamily_infinite q⟩

end Case019Work
