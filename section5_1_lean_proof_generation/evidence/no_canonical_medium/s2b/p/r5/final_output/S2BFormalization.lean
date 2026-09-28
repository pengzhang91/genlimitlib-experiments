import Stage3Model
import Mathlib.Data.Nat.Nth
import Mathlib.Analysis.SpecificLimits.Normed

open Set Filter
open GenLimit.KleinbergWei

namespace Stage3Proof
open Stage3S2B

private def extend {α : Type} {t : ℕ} (f : Fin t → α) (a : α) : Fin (t+1) → α :=
  Fin.lastCases a f

private lemma extend_castSucc {α : Type} {t : ℕ} (f : Fin t → α) (a : α) (i : Fin t) :
    extend f a i.castSucc = f i := by simp [extend]
private lemma extend_last {α : Type} {t : ℕ} (f : Fin t → α) (a : α) :
    extend f a (Fin.last t) = a := by simp [extend]

structure Hist (t : ℕ) where
  x : Fin t → ℕ
  q : Fin t → Option ℕ
  a : Fin t → Option Bool
  y : Fin t → ℕ
  rejected : Finset ℕ
  x_inj : Function.Injective x
  x_not_rejected : ∀ i, x i ∉ rejected

private def used {t : ℕ} (h : Hist t) : Finset ℕ := Finset.univ.image h.x ∪ h.rejected

private lemma nextVal_exists {t : ℕ} (h : Hist t) : ∃ z, z ∉ used h := by
  let M := (used h).sup id
  refine ⟨M+1, ?_⟩
  intro hm
  have hle : M+1 ≤ M := Finset.le_sup (f := id) hm
  omega

private def nextVal {t : ℕ} (h : Hist t) : ℕ := Nat.find (nextVal_exists h)

private lemma nextVal_not_used {t : ℕ} (h : Hist t) : nextVal h ∉ used h := by
  exact Nat.find_spec (nextVal_exists h)
private lemma nextVal_fresh {t : ℕ} (h : Hist t) (i : Fin t) : nextVal h ≠ h.x i := by
  intro he
  apply nextVal_not_used h
  rw [he]
  simp [used]

private lemma nextVal_not_rejected {t : ℕ} (h : Hist t) : nextVal h ∉ h.rejected := by
  intro hz
  exact nextVal_not_used h (by simp [used, hz])

private noncomputable def addReject {t : ℕ} (x : Fin t → ℕ) (s : Finset ℕ) (w : ℕ) : Finset ℕ := by
  classical
  exact if w ∈ core ∨ w ∈ Finset.univ.image x then s else insert w s


private lemma addReject_preserves {t : ℕ} (x : Fin t → ℕ) (s : Finset ℕ) (w v : ℕ)
    (hv : v ∈ Finset.univ.image x) (hs : v ∉ s) : v ∉ addReject x s w := by
  classical
  simp only [addReject]
  split
  · exact hs
  · simp only [Finset.mem_insert, not_or]
    exact ⟨fun he => ‹¬ (w ∈ core ∨ w ∈ Finset.univ.image x)› (Or.inr (he ▸ hv)), hs⟩

private lemma extend_injective {α : Type} {t : ℕ} (f : Fin t → α) (a : α)
    (hf : Function.Injective f) (ha : ∀ i, a ≠ f i) : Function.Injective (extend f a) := by
  intro i j hij
  by_cases hi : i = Fin.last t
  · subst i
    by_cases hj : j = Fin.last t
    · exact hj.symm
    · obtain ⟨j0, rfl⟩ := Fin.exists_castSucc_eq.mpr hj
      simp only [extend_last, extend_castSucc] at hij
      exact False.elim (ha j0 hij)
  · obtain ⟨i0, rfl⟩ := Fin.exists_castSucc_eq.mpr hi
    by_cases hj : j = Fin.last t
    · subst j
      simp only [extend_castSucc, extend_last] at hij
      exact False.elim (ha i0 hij.symm)
    · obtain ⟨j0, rfl⟩ := Fin.exists_castSucc_eq.mpr hj
      exact congrArg (fun k : Fin t => k.castSucc) (hf (by simpa only [extend_castSucc] using hij))

noncomputable def step (gen : FeedbackGenerator) {t : ℕ} (h : Hist t) : Hist (t+1) := by
  classical
  let z := nextVal h
  let x' := extend h.x z
  let qz := gen.query t x' h.a
  let az : Option Bool := match qz with
    | none => none
    | some w => some (decide (w ∈ core ∨ w ∈ Finset.univ.image x'))
  let a' := extend h.a az
  let yz := gen.output t x' a'
  let r1 := match qz with
    | none => h.rejected
    | some w => addReject x' h.rejected w
  let r2 := addReject x' r1 yz
  refine Hist.mk x' (extend h.q qz) a' (extend h.y yz) r2 ?_ ?_
  · exact extend_injective h.x z h.x_inj (nextVal_fresh h)
  · intro i
    have hi : x' i ∈ Finset.univ.image x' := by simp
    have h0 : x' i ∉ h.rejected := by
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa [x', extend_last] using nextVal_not_rejected h
      · simpa [x', extend_castSucc] using h.x_not_rejected j
    have h1 : x' i ∉ r1 := by
      cases hq : qz with
      | none => simpa [r1, hq] using h0
      | some w =>
          simpa [r1, hq] using addReject_preserves x' h.rejected w _ hi h0
    exact addReject_preserves x' r1 yz _ hi h1
noncomputable def run (gen : FeedbackGenerator) : (t : ℕ) → Hist t
  | 0 => Hist.mk Fin.elim0 Fin.elim0 Fin.elim0 Fin.elim0 ∅
      (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
  | t+1 => step gen (run gen t)

noncomputable def presentation (gen : FeedbackGenerator) (t : ℕ) : ℕ :=
  (run gen (t+1)).x (Fin.last t)
noncomputable def queries (gen : FeedbackGenerator) (t : ℕ) : Option ℕ :=
  (run gen (t+1)).q (Fin.last t)
noncomputable def answers (gen : FeedbackGenerator) (t : ℕ) : Option Bool :=
  (run gen (t+1)).a (Fin.last t)
noncomputable def outputs (gen : FeedbackGenerator) (t : ℕ) : ℕ :=
  (run gen (t+1)).y (Fin.last t)

lemma core_injective : Function.Injective (fun k : ℕ => 2^k) := by
  intro a b h
  exact (Nat.pow_right_injective (by omega : 1 < 2)) h

lemma uniform_generation : UniformlyGeneratableWithoutSamples := by
  refine ⟨fun k => 2^k, core_injective, 0, ?_⟩
  intro K hK t ht
  rcases hK with ⟨A, hA, rfl⟩
  exact Or.inl ⟨t, rfl⟩

lemma code_ordinary (n : ℕ) : 2*n+3 ∈ ordinary := by
  intro hcore
  rcases hcore with ⟨k, hk⟩
  cases k with
  | zero => simp at hk
  | succ j =>
      change 2 ^ (j+1) = 2*n+3 at hk
      rw [pow_succ] at hk
      omega

lemma targetClass_uncountable : ¬ targetClass.Countable := by
  intro hc
  have hne : targetClass.Nonempty := ⟨core, ∅, empty_subset _, by simp⟩
  obtain ⟨f, hf⟩ := hc.exists_surjective hne
  let code : ℕ → ℕ := fun n => 2*n+3
  let A : Set ℕ := {z | ∃ n, z = code n ∧ z ∉ (f n : Set ℕ)}
  let K : Set ℕ := core ∪ A
  have hK : K ∈ targetClass := ⟨A, by
    rintro z ⟨n, rfl, hn⟩
    exact code_ordinary n, rfl⟩
  obtain ⟨n, hn⟩ := hf ⟨K, hK⟩
  have hd := Set.ext_iff.mp (congrArg Subtype.val hn) (code n)
  have hcnot : code n ∉ core := code_ordinary n
  have hmem : code n ∈ K ↔ code n ∉ (f n : Set ℕ) := by
    simp [K, A, hcnot, code]
  
  exact not_iff_self (hmem.symm.trans hd.symm)

end Stage3Proof



open Stage3Proof

/-- Checked positive portion of `Stage3S2B.MainClaim`. -/
theorem stage3_positive :
    ¬ Stage3S2B.targetClass.Countable ∧
      Stage3S2B.UniformlyGeneratableWithoutSamples :=
  ⟨targetClass_uncountable, uniform_generation⟩
