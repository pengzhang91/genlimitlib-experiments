/-
E12 round 2: machine-checked answer keys.
Each theorem pins the key of one question. Compiled against the pinned library.
-/
import GenLimit.Paper06_NoisyExamples.Definitions
import GenLimit.Core.VersionSpace
import GenLimit.Core.ClosureDimension
import GenLimit.Core.ClassGeneration

namespace E12.Keys

open GenLimit.Generic
open GenLimit.NoisyExamples

variable {α : Type*}

/-! ### Direction facts about version spaces and cores -/

/-- K01. The version space is ANTITONE in the sample: more observations admit
fewer languages. -/
theorem versionSpace_antitone (H : LanguageClass α) {S T : Finset α} (h : S ⊆ T) :
    versionSpace H T ⊆ versionSpace H S :=
  fun _ hL => ⟨hL.1, fun _ hx => hL.2 (h hx)⟩

/-- K02. Hence the common core is MONOTONE in the sample: more observations give
a LARGER core, because the intersection runs over fewer languages. -/
theorem commonCore_monotone (H : LanguageClass α) {S T : Finset α} (h : S ⊆ T) :
    commonCore H S ⊆ commonCore H T :=
  fun _ hx L hL => hx L (versionSpace_antitone H h hL)

/-- K03. The sample is always contained in its own common core, with no
consistency hypothesis. -/
theorem subset_commonCore (H : LanguageClass α) (S : Finset α) :
    (↑S : Set α) ⊆ commonCore H S :=
  fun _ hx L hL => hL.2 hx

/-- K04. The common core is contained in every language of its version space. -/
theorem commonCore_subset_of_mem (H : LanguageClass α) (S : Finset α)
    {L : Language α} (hL : L ∈ versionSpace H S) :
    commonCore H S ⊆ L :=
  fun _ hx => hx L hL

/-- K05. An empty version space forces the common core to be everything: the
intersection of an empty family is the universe, which is why the papers carry a
separate bottom symbol. -/
theorem commonCore_eq_univ_of_empty (H : LanguageClass α) (S : Finset α)
    (h : versionSpace H S = ∅) :
    commonCore H S = Set.univ := by
  ext x; simp only [commonCore, Set.mem_setOf_eq, Set.mem_univ, iff_true]
  intro L hL; rw [h] at hL; exact absurd hL (Set.notMem_empty L)

/-! ### Noise level: specialization and direction -/

/-- K06. Paper 06's noisy version space at n = 0 IS Paper 02's version space. -/
theorem noisyVersionSpace_zero_eq_versionSpace (H : LanguageClass α) (S : Finset α) :
    noisyVersionSpace H S 0 = versionSpace H S := by
  classical
  ext L
  simp only [noisyVersionSpace, versionSpace, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hH, hcard⟩
    refine ⟨hH, ?_⟩
    have hsub : positivePart S L ⊆ S := fun x hx => (Finset.mem_filter.mp hx).1
    have hEq : positivePart S L = S :=
      Finset.eq_of_subset_of_card_le hsub (by simpa using hcard)
    intro x hx
    have : x ∈ positivePart S L := by rw [hEq]; exact hx
    exact (Finset.mem_filter.mp this).2
  · rintro ⟨hH, hsub⟩
    refine ⟨hH, ?_⟩
    have hEq : positivePart S L = S :=
      Finset.filter_true_of_mem fun x hx => hsub hx
    simp [hEq]

/-- K07. The two common cores agree at noise level 0. -/
theorem noisyCommonCore_zero_eq_commonCore (H : LanguageClass α) (S : Finset α) :
    noisyCommonCore H S 0 = commonCore H S := by
  ext x
  simp only [noisyCommonCore, commonCore, Set.mem_setOf_eq,
    noisyVersionSpace_zero_eq_versionSpace]

/-- K08. The noisy version space GROWS with the noise level. -/
theorem noisyVersionSpace_mono (H : LanguageClass α) (S : Finset α) {m n : ℕ} (h : m ≤ n) :
    noisyVersionSpace H S m ⊆ noisyVersionSpace H S n :=
  fun _ hL => ⟨hL.1, le_trans hL.2 (by omega)⟩

/-- K09. Hence the noisy common core SHRINKS as the noise level grows. -/
theorem noisyCommonCore_antitone (H : LanguageClass α) (S : Finset α) {m n : ℕ} (h : m ≤ n) :
    noisyCommonCore H S n ⊆ noisyCommonCore H S m :=
  fun _ hx L hL => hx L (noisyVersionSpace_mono H S h hL)

/-- K10. Paper 02's version space is the smallest member of Paper 06's family. -/
theorem versionSpace_subset_noisyVersionSpace (H : LanguageClass α) (S : Finset α) (n : ℕ) :
    versionSpace H S ⊆ noisyVersionSpace H S n := by
  rw [← noisyVersionSpace_zero_eq_versionSpace]; exact noisyVersionSpace_mono H S (Nat.zero_le n)

/-- K11. The noisy core at any level is contained in Paper 02's core. -/
theorem noisyCommonCore_subset_commonCore (H : LanguageClass α) (S : Finset α) (n : ℕ) :
    noisyCommonCore H S n ⊆ commonCore H S :=
  fun _ hx L hL => hx L (versionSpace_subset_noisyVersionSpace H S n hL)

/-! ### Closure dimension -/

/-- K12. Noisy closure witnesses at n = 0 are exactly Core closure witnesses. -/
theorem noisyClosureWitnessAt_zero_iff (H : LanguageClass α) (d : ℕ) :
    NoisyClosureWitnessAt H 0 d ↔ ∃ S : Finset α, S.card = d ∧ IsClosureWitness H S := by
  simp only [NoisyClosureWitnessAt, IsClosureWitness,
    noisyVersionSpace_zero_eq_versionSpace, noisyCommonCore_zero_eq_commonCore]

/-- K13. Noisy closure witnesses are monotone in the noise level, so `NC_n(H)` is
NON-DECREASING in n. -/
theorem noisyClosureWitnessAt_mono (H : LanguageClass α) {m n : ℕ} (hmn : m ≤ n) (d : ℕ)
    (h : NoisyClosureWitnessAt H m d) : NoisyClosureWitnessAt H n d := by
  obtain ⟨S, hcard, ⟨L, hL⟩, hfin⟩ := h
  exact ⟨S, hcard, ⟨L, noisyVersionSpace_mono H S hmn hL⟩,
    hfin.subset (noisyCommonCore_antitone H S hmn)⟩

/-- K14. `NC_0(H) < infinity` holds exactly when `C(H)` is finite. -/
theorem finiteNoisyClosureDimensionAt_zero_iff (H : LanguageClass α) :
    FiniteNoisyClosureDimensionAt H 0 ↔ HasFiniteClosureDimension H := by
  classical
  rw [finite_closure_dimension_iff_not_infinite]
  simp only [FiniteNoisyClosureDimensionAt, noisyClosureWitnessAt_zero_iff,
    HasInfiniteClosureDimension]
  constructor
  · rintro ⟨D, hD⟩ hInf
    obtain ⟨S, hcard, hS⟩ := hInf (D + 1)
    obtain ⟨T, hTS, hTcard⟩ := Finset.exists_subset_card_eq hcard
    exact hD (D + 1) (by omega) ⟨T, hTcard, closure_witness_mono hTS hS⟩
  · intro hNot
    by_contra hcon
    push_neg at hcon
    refine hNot fun d => ?_
    obtain ⟨e, hde, S, hcard, hS⟩ := hcon d
    exact ⟨S, by omega, hS⟩

/-- K15. Finiteness of the noisy closure dimension is ANTITONE in n: finiteness at
a higher noise level implies finiteness at every lower one. -/
theorem finiteNoisyClosureDimensionAt_antitone (H : LanguageClass α) {m n : ℕ} (hmn : m ≤ n)
    (h : FiniteNoisyClosureDimensionAt H n) : FiniteNoisyClosureDimensionAt H m := by
  obtain ⟨D, hD⟩ := h
  exact ⟨D, fun d hd hw => hD d hd (noisyClosureWitnessAt_mono H hmn d hw)⟩

/-! ### Generatability notions -/

/-- K16. Uniform generation implies non-uniform generation: move the common
threshold inside the target quantifier. -/
theorem uniform_implies_nonuniform (H : LanguageClass α)
    (h : UniformlyGeneratable H) : NonuniformlyGeneratable H := by
  obtain ⟨gen, d, hgen⟩ := h
  exact ⟨gen, fun L hL => ⟨d, fun stream hs t ht s hts => hgen L hL stream hs t ht s hts⟩⟩

/-- K17. A closure witness restricts to every subset of its sample. -/
theorem closure_witness_subset (H : LanguageClass α) {S T : Finset α}
    (hST : S ⊆ T) (hT : IsClosureWitness H T) : IsClosureWitness H S :=
  closure_witness_mono hST hT

end E12.Keys

#print axioms E12.Keys.versionSpace_antitone
#print axioms E12.Keys.commonCore_monotone
#print axioms E12.Keys.subset_commonCore
#print axioms E12.Keys.commonCore_subset_of_mem
#print axioms E12.Keys.commonCore_eq_univ_of_empty
#print axioms E12.Keys.noisyVersionSpace_zero_eq_versionSpace
#print axioms E12.Keys.noisyCommonCore_zero_eq_commonCore
#print axioms E12.Keys.noisyVersionSpace_mono
#print axioms E12.Keys.noisyCommonCore_antitone
#print axioms E12.Keys.versionSpace_subset_noisyVersionSpace
#print axioms E12.Keys.noisyCommonCore_subset_commonCore
#print axioms E12.Keys.noisyClosureWitnessAt_zero_iff
#print axioms E12.Keys.noisyClosureWitnessAt_mono
#print axioms E12.Keys.finiteNoisyClosureDimensionAt_zero_iff
#print axioms E12.Keys.finiteNoisyClosureDimensionAt_antitone
#print axioms E12.Keys.uniform_implies_nonuniform
#print axioms E12.Keys.closure_witness_subset
