import Stage3Model

open Set
open Stage3Case019

namespace Case019

def markers (q : ℕ) : Set ℤ := {z | ∃ n ≤ q, z = Int.ofNat n}

def positiveTail (j : ℕ) : Set ℤ := {z | Int.ofNat j < z}

def negativeRay : Set ℤ := {z | z < 0}

def upperLanguages (q : ℕ) : Set (Set ℤ) :=
  {K | ∃ j A, K = markers q ∪ A ∪ positiveTail j}

def lowerLanguages (q : ℕ) : Set (Set ℤ) :=
  {K | ∃ A, A ⊆ (markers q)ᶜ ∧ K = A ∪ negativeRay}

def separatingFamily (q : ℕ) : Set (Set ℤ) :=
  upperLanguages q ∪ lowerLanguages q

lemma marker_mem {q n : ℕ} (hn : n ≤ q) : Int.ofNat n ∈ markers q := by
  exact ⟨n, hn, rfl⟩

lemma marker_nonneg {q : ℕ} {z : ℤ} (hz : z ∈ markers q) : 0 ≤ z := by
  rcases hz with ⟨n, -, rfl⟩
  exact Int.natCast_nonneg n

lemma negative_not_marker {q : ℕ} {z : ℤ} (hz : z < 0) : z ∉ markers q := by
  intro h
  exact (not_le_of_gt hz) (marker_nonneg h)

lemma positiveTail_infinite (j : ℕ) : (positiveTail j).Infinite := by
  have hinj : Function.Injective (fun n : ℕ => Int.ofNat (j + n + 1)) := by
    intro a b hab
    simp only [Int.ofNat.injEq, Nat.add_left_cancel_iff, Nat.add_right_cancel_iff] at hab
    exact hab
  have hrange : Set.range (fun n : ℕ => Int.ofNat (j + n + 1)) ⊆ positiveTail j := by
    rintro z ⟨n, rfl⟩
    simp only [positiveTail, Set.mem_setOf_eq]
    have h : j < j + n + 1 := by omega
    exact Int.ofNat_lt.mpr h
  exact (Set.infinite_range_of_injective hinj).mono hrange

lemma negativeRay_infinite : negativeRay.Infinite := by
  have hinj : Function.Injective (fun n : ℕ => -(Int.ofNat n) - 1) := by
    intro a b hab
    have hneg : -Int.ofNat a = -Int.ofNat b := sub_left_injective hab
    have hnat : Int.ofNat a = Int.ofNat b := neg_injective hneg
    simpa using hnat
  have hrange : Set.range (fun n : ℕ => -(Int.ofNat n) - 1) ⊆ negativeRay := by
    rintro z ⟨n, rfl⟩
    simp only [negativeRay, Set.mem_setOf_eq]
    have hn : (0 : ℤ) ≤ Int.ofNat n := Int.natCast_nonneg n
    omega
  exact (Set.infinite_range_of_injective hinj).mono hrange


def codeLanguage (q : ℕ) (A : Set ℕ) : Set ℤ :=
  {z | ∃ n ∈ A, z = Int.ofNat (q + 1 + n)} ∪ negativeRay

lemma codeLanguage_mem (q : ℕ) (A : Set ℕ) :
    codeLanguage q A ∈ separatingFamily q := by
  apply Or.inr
  refine ⟨{z | ∃ n ∈ A, z = Int.ofNat (q + 1 + n)}, ?_, rfl⟩
  intro z hz
  rcases hz with ⟨n, hn, rfl⟩
  intro hmarker
  rcases hmarker with ⟨m, hm, heq⟩
  have hcast : Int.ofNat (q + 1 + n) = Int.ofNat m := heq
  have : q + 1 + n = m := Int.ofNat.inj hcast
  omega

lemma codeLanguage_injective (q : ℕ) : Function.Injective (codeLanguage q) := by
  intro A B hAB
  ext n
  let z := Int.ofNat (q + 1 + n)
  have hzneg : ¬z ∈ negativeRay := by
    simp only [z, negativeRay, Set.mem_setOf_eq, not_lt]
    exact Int.natCast_nonneg (q + 1 + n)
  have hzA : z ∈ codeLanguage q A ↔ n ∈ A := by
    constructor
    · intro hz
      rcases hz with hz | hz
      · rcases hz with ⟨m, hm, heq⟩
        have : q + 1 + n = q + 1 + m := by simpa [z] using heq
        have : m = n := by omega
        simpa [this] using hm
      · exact (hzneg hz).elim
    · intro hn
      exact Or.inl ⟨n, hn, rfl⟩
  have hzB : z ∈ codeLanguage q B ↔ n ∈ B := by
    constructor
    · intro hz
      rcases hz with hz | hz
      · rcases hz with ⟨m, hm, heq⟩
        have : q + 1 + n = q + 1 + m := by simpa [z] using heq
        have : m = n := by omega
        simpa [this] using hm
      · exact (hzneg hz).elim
    · intro hn
      exact Or.inl ⟨n, hn, rfl⟩
  rw [← hzA, hAB, hzB]

lemma separatingFamily_uncountable (q : ℕ) : ¬(separatingFamily q).Countable := by
  intro hcount
  have hmaps : MapsTo (codeLanguage q) Set.univ (separatingFamily q) := by
    intro A hA
    exact codeLanguage_mem q A
  have hinj : Set.InjOn (codeLanguage q) Set.univ :=
    (codeLanguage_injective q).injOn
  have huniv : (Set.univ : Set (Set ℕ)).Countable :=
    hmaps.countable_of_injOn hinj hcount
  rcases huniv.exists_surjective (Set.univ_nonempty : (Set.univ : Set (Set ℕ)).Nonempty) with
    ⟨f, hf⟩
  let D : Set ℕ := {n | n ∉ (f n : Set ℕ)}
  rcases hf ⟨D, Set.mem_univ D⟩ with ⟨k, hk⟩
  have hset : (f k : Set ℕ) = D := congrArg Subtype.val hk
  have hdiag : k ∈ D ↔ k ∉ D := by
    change k ∉ (f k : Set ℕ) ↔ k ∉ D
    rw [hset]
  by_cases hkD : k ∈ D
  · exact (hdiag.mp hkD) hkD
  · exact hkD (hdiag.mpr hkD)

lemma separatingFamily_infinite_languages (q : ℕ) :
    ∀ K ∈ separatingFamily q, K.Infinite := by
  intro K hK
  rcases hK with hK | hK
  · rcases hK with ⟨j, A, rfl⟩
    exact (positiveTail_infinite j).mono (by intro z hz; exact Or.inr hz)
  · rcases hK with ⟨A, hA, rfl⟩
    exact negativeRay_infinite.mono (by intro z hz; exact Or.inr hz)

end Case019

/-- Checked structural part of the separation witness: for every noise level,
there is an extensional uncountable family consisting entirely of infinite
integer languages. -/
theorem stage3_separation_family_structure (q : ℕ) :
    ∃ family : Stage3Case019.LanguageClass ℤ,
      ¬family.Countable ∧ ∀ K ∈ family, K.Infinite := by
  exact ⟨Case019.separatingFamily q,
    Case019.separatingFamily_uncountable q,
    Case019.separatingFamily_infinite_languages q⟩
