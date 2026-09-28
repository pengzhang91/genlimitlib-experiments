import Stage3Model
import Mathlib.Data.Nat.Nth
import Mathlib.SetTheory.Cardinal.Continuum

open Set Filter
open GenLimit.KleinbergWei

namespace S2BProof

open Stage3S2B

private def candidate (n : ℕ) : ℕ := 2 * n + 3

private theorem candidate_injective : Function.Injective candidate := by
  intro a b h
  dsimp [candidate] at h
  omega

private theorem candidate_ordinary (n : ℕ) : candidate n ∈ ordinary := by
  intro h
  rcases h with ⟨k, hk⟩
  dsimp [candidate] at hk
  cases k with
  | zero => omega
  | succ k =>
      have heven : Even (2 ^ (k + 1)) := by
        refine ⟨2 ^ k, by rw [pow_succ]; omega⟩
      have hodd : Odd (2 * n + 3) := ⟨n + 1, by omega⟩
      rw [← hk] at hodd
      rw [Nat.even_iff] at heven
      rw [Nat.odd_iff] at hodd
      omega

private def forbidden {t : ℕ} (x : Fin t → ℕ) (q : Fin t → Option ℕ)
    (y : Fin t → ℕ) : Finset ℕ := by
  classical
  exact (Finset.univ.image x) ∪
    (Finset.univ.biUnion fun i => (q i).toFinset) ∪
    (Finset.univ.image y)

private theorem exists_fresh {t : ℕ} (x : Fin t → ℕ) (q : Fin t → Option ℕ)
    (y : Fin t → ℕ) : ∃ n, candidate n ∉ forbidden x q y := by
  classical
  obtain ⟨z, ⟨n, rfl⟩, hn⟩ :=
    (Set.infinite_range_of_injective candidate_injective).exists_not_mem_finset
      (forbidden x q y)
  exact ⟨n, hn⟩

private noncomputable def freshIndex {t : ℕ} (x : Fin t → ℕ)
    (q : Fin t → Option ℕ) (y : Fin t → ℕ) : ℕ :=
  Nat.find (exists_fresh x q y)

private noncomputable def adaptivePresenter : CausalPresenter where
  next t x q _ y := if Even t then 2 ^ (t / 2) else candidate (freshIndex x q y)

private structure Hist (t : ℕ) where
  x : Fin t → ℕ
  q : Fin t → Option ℕ
  a : Fin t → Option Bool
  y : Fin t → ℕ

private def Hist.nil : Hist 0 where
  x := Fin.elim0
  q := Fin.elim0
  a := Fin.elim0
  y := Fin.elim0

private def Hist.snoc {t : ℕ} (h : Hist t) (x : ℕ) (q : Option ℕ)
    (a : Option Bool) (y : ℕ) : Hist (t + 1) where
  x := Fin.lastCases x h.x
  q := Fin.lastCases q h.q
  a := Fin.lastCases a h.a
  y := Fin.lastCases y h.y

private noncomputable def build (gen : FeedbackGenerator) : (t : ℕ) → Hist t
  | 0 => Hist.nil
  | t + 1 =>
      let h := build gen t
      let x := adaptivePresenter.next t h.x h.q h.a h.y
      let xs : Fin (t + 1) → ℕ := Fin.lastCases x h.x
      let q := gen.query t xs h.a
      let a := match q with
        | none => none
        | some z => some (membershipAnswer
            (core ∪ {z | ∃ i : Fin (t + 1), xs i = z}) z)
      let y := gen.output t xs (Fin.lastCases a h.a)
      h.snoc x q a y

private noncomputable def diagonalTranscript (gen : FeedbackGenerator) : Transcript where
  presentation t := (build gen (t + 1)).x (Fin.last t)
  query t := (build gen (t + 1)).q (Fin.last t)
  answer t := (build gen (t + 1)).a (Fin.last t)
  output t := (build gen (t + 1)).y (Fin.last t)

private noncomputable def diagonalTarget (gen : FeedbackGenerator) : Language :=
  core ∪ {z | ∃ r, (diagonalTranscript gen).presentation (2 * r + 1) = z}



private def encodeTarget (A : Set ℕ) : Language := core ∪ candidate '' A

private theorem encodeTarget_mem (A : Set ℕ) : encodeTarget A ∈ targetClass := by
  refine ⟨candidate '' A, ?_, rfl⟩
  intro z hz
  rcases hz with ⟨n, _, rfl⟩
  exact candidate_ordinary n

private theorem encodeTarget_injective : Function.Injective encodeTarget := by
  intro A B h
  ext n
  have hn : candidate n ∉ core := candidate_ordinary n
  have hiA : candidate n ∈ candidate '' A ↔ n ∈ A := by
    constructor
    · rintro ⟨m, hm, heq⟩
      exact (candidate_injective heq).symm ▸ hm
    · exact fun hm => ⟨n, hm, rfl⟩
  have hiB : candidate n ∈ candidate '' B ↔ n ∈ B := by
    constructor
    · rintro ⟨m, hm, heq⟩
      exact (candidate_injective heq).symm ▸ hm
    · exact fun hm => ⟨n, hm, rfl⟩
  have := Set.ext_iff.mp h (candidate n)
  simpa [encodeTarget, hn, hiA, hiB] using this

private theorem targetClass_uncountable : ¬ targetClass.Countable := by
  letI : Uncountable (Set ℕ) := Cardinal.aleph0_lt_mk_iff.mp (by
    rw [Cardinal.mk_set_nat]
    exact Cardinal.aleph0_lt_continuum)
  intro h
  have hp := h.preimage encodeTarget_injective
  have hall : encodeTarget ⁻¹' targetClass = Set.univ := by
    ext A
    simp [encodeTarget_mem]
  rw [hall] at hp
  exact Set.not_countable_univ hp

private theorem uniform_positive : UniformlyGeneratableWithoutSamples := by
  refine ⟨fun t => 2 ^ t, ?_, 0, ?_⟩
  · intro a b hab
    apply le_antisymm
    · by_contra hba
      have hlt : b < a := Nat.lt_of_not_ge hba
      exact (Nat.pow_lt_pow_right (by omega) hlt).ne hab.symm
    · by_contra hab'
      have hlt : a < b := Nat.lt_of_not_ge hab'
      exact (Nat.pow_lt_pow_right (by omega) hlt).ne hab
  · intro K hK t _
    rcases hK with ⟨A, hA, rfl⟩
    exact Or.inl ⟨t, rfl⟩


end S2BProof

open Stage3S2B

theorem stage3_positive_partial :
    ¬ targetClass.Countable ∧ UniformlyGeneratableWithoutSamples := by
  exact ⟨S2BProof.targetClass_uncountable, S2BProof.uniform_positive⟩

theorem stage3_result : Stage3S2B.MainClaim := by
  sorry
