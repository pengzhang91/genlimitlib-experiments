import Stage3Model
import GenLimit.Paper10_UnionClosednessOfLanguageGeneration.Cardinality

open Set Filter
open GenLimit.KleinbergWei

namespace Stage3Proof
open Stage3S2B

lemma pow_two_injective : Function.Injective (fun k : ℕ => 2 ^ k) := by
  intro a b h
  exact Nat.pow_right_injective (by omega) h

lemma core_mem (k : ℕ) : 2 ^ k ∈ core := ⟨k, rfl⟩

lemma odd_three_not_core (n : ℕ) : 2 * n + 3 ∈ ordinary := by
  rintro ⟨k, hk⟩
  cases k with
  | zero => simp at hk
  | succ k =>
      change 2 ^ (k + 1) = 2 * n + 3 at hk
      have hd : 2 ∣ 2 ^ (k + 1) := dvd_pow_self 2 (by omega)
      rw [hk] at hd
      omega

lemma ordinary_infinite : ordinary.Infinite := by
  apply Set.infinite_of_injective_forall_mem (f := fun n : ℕ => 2*n+3)
  · intro a b h
    simp only at h
    omega
  · exact odd_three_not_core

noncomputable def freshOrdinary (S : Finset ℕ) : ℕ := by
  classical
  exact Nat.find (ordinary_infinite.exists_notMem_finset S)

lemma freshOrdinary_spec (S : Finset ℕ) :
    freshOrdinary S ∈ ordinary ∧ freshOrdinary S ∉ S := by
  classical
  exact Nat.find_spec (ordinary_infinite.exists_notMem_finset S)

structure St (gen : FeedbackGenerator) (t : ℕ) where
  x : Fin t → ℕ
  q : Fin t → Option ℕ
  b : Fin t → Option Bool
  y : Fin t → ℕ
  I : Finset ℕ
  R : Finset ℕ

def emptySt (gen : FeedbackGenerator) : St gen 0 where
  x := Fin.elim0
  q := Fin.elim0
  b := Fin.elim0
  y := Fin.elim0
  I := ∅
  R := ∅

noncomputable def xv (gen : FeedbackGenerator) {t : ℕ} (s : St gen t) : ℕ :=
  if Even t then 2 ^ (t / 2) else freshOrdinary (s.I ∪ s.R)

noncomputable def Iminus (gen : FeedbackGenerator) {t : ℕ} (s : St gen t) : Finset ℕ :=
  if Even t then s.I else insert (xv gen s) s.I

noncomputable def qv (gen : FeedbackGenerator) {t : ℕ} (s : St gen t) : Option ℕ :=
  gen.query t (Fin.snoc s.x (xv gen s)) s.b

noncomputable def bv (gen : FeedbackGenerator) {t : ℕ} (s : St gen t) : Option Bool := by
  classical
  exact (qv gen s).map fun z => decide (z ∈ core ∨ z ∈ Iminus gen s)

noncomputable def Rq (gen : FeedbackGenerator) {t : ℕ} (s : St gen t) : Finset ℕ := by
  classical
  exact match qv gen s with
  | none => s.R
  | some z => if z ∈ core ∨ z ∈ Iminus gen s ∨ z ∈ s.R then s.R else insert z s.R

noncomputable def yv (gen : FeedbackGenerator) {t : ℕ} (s : St gen t) : ℕ :=
  gen.output t (Fin.snoc s.x (xv gen s)) (Fin.snoc s.b (bv gen s))

noncomputable def Rnext (gen : FeedbackGenerator) {t : ℕ} (s : St gen t) : Finset ℕ := by
  classical
  exact if yv gen s ∈ core ∨ yv gen s ∈ Iminus gen s ∨ yv gen s ∈ Rq gen s
    then Rq gen s else insert (yv gen s) (Rq gen s)

noncomputable def step (gen : FeedbackGenerator) {t : ℕ} (s : St gen t) : St gen (t+1) := {
  x := Fin.snoc s.x (xv gen s)
  q := Fin.snoc s.q (qv gen s)
  b := Fin.snoc s.b (bv gen s)
  y := Fin.snoc s.y (yv gen s)
  I := Iminus gen s
  R := Rnext gen s }

noncomputable def st (gen : FeedbackGenerator) : (t : ℕ) → St gen t
  | 0 => emptySt gen
  | t+1 => step gen (st gen t)

noncomputable def tr (gen : FeedbackGenerator) : Transcript where
  presentation t := (st gen (t+1)).x (Fin.last t)
  query t := (st gen (t+1)).q (Fin.last t)
  answer t := (st gen (t+1)).b (Fin.last t)
  output t := (st gen (t+1)).y (Fin.last t)

noncomputable def K (gen : FeedbackGenerator) : Language :=
  core ∪ {z | ∃ t, z ∈ (st gen t).I}

noncomputable def presenter (gen : FeedbackGenerator) : CausalPresenter where
  next t _ _ _ _ := (tr gen).presentation t


lemma prefix_x (gen : FeedbackGenerator) (t : ℕ) :
    (fun i : Fin t => (tr gen).presentation i) = (st gen t).x := by
  induction t with
  | zero => funext i; exact Fin.elim0 i
  | succ t ih =>
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [tr, st, step, xv, qv, bv, yv]
      · simp [tr, st, step, ← congrFun ih j]

lemma prefix_q (gen : FeedbackGenerator) (t : ℕ) :
    (fun i : Fin t => (tr gen).query i) = (st gen t).q := by
  induction t with
  | zero => funext i; exact Fin.elim0 i
  | succ t ih =>
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [tr, st, step, xv, qv, bv, yv]
      · simp [tr, st, step, ← congrFun ih j]

lemma prefix_b (gen : FeedbackGenerator) (t : ℕ) :
    (fun i : Fin t => (tr gen).answer i) = (st gen t).b := by
  induction t with
  | zero => funext i; exact Fin.elim0 i
  | succ t ih =>
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [tr, st, step, xv, qv, bv, yv]
      · simp [tr, st, step, ← congrFun ih j]

lemma prefix_y (gen : FeedbackGenerator) (t : ℕ) :
    (fun i : Fin t => (tr gen).output i) = (st gen t).y := by
  induction t with
  | zero => funext i; exact Fin.elim0 i
  | succ t ih =>
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [tr, st, step, xv, qv, bv, yv]
      · simp [tr, st, step, ← congrFun ih j]

lemma presentation_formula (gen : FeedbackGenerator) (t : ℕ) :
    (tr gen).presentation t =
      if Even t then 2 ^ (t / 2) else freshOrdinary ((st gen t).I ∪ (st gen t).R) := by
  simp [tr, st, step, xv, qv, bv, yv]

lemma query_formula (gen : FeedbackGenerator) (t : ℕ) :
    (tr gen).query t = gen.query t
      (fun i => (tr gen).presentation i) (fun i => (tr gen).answer i) := by
  rw [prefix_x, prefix_b]
  simp [tr, st, step, xv, qv, bv, yv]

lemma output_formula (gen : FeedbackGenerator) (t : ℕ) :
    (tr gen).output t = gen.output t
      (fun i => (tr gen).presentation i) (fun i => (tr gen).answer i) := by
  rw [prefix_x, prefix_b]
  simp [tr, st, step, xv, qv, bv, yv]



lemma Iminus_props (gen : FeedbackGenerator) {t : ℕ} (s : St gen t)
    (hI : ∀ z ∈ s.I, z ∈ ordinary) (hdis : Disjoint s.I s.R) :
    (∀ z ∈ Iminus gen s, z ∈ ordinary) ∧ Disjoint (Iminus gen s) s.R := by
  by_cases he : Even t
  · constructor
    · simpa [Iminus, he] using hI
    · simpa [Iminus, he] using hdis
  · have hf := freshOrdinary_spec (s.I ∪ s.R)
    constructor
    · intro z hz
      simp [Iminus, he] at hz
      rcases hz with rfl | hz
      · simpa [xv, he] using hf.1
      · exact hI z hz
    · rw [Finset.disjoint_left]
      intro z hzI hzR
      simp [Iminus, he] at hzI
      rcases hzI with rfl | hzI
      · apply hf.2
        apply Finset.mem_union_right s.I
        simpa [xv, he] using hzR
      · exact (Finset.disjoint_left.mp hdis) hzI hzR

lemma Rq_props (gen : FeedbackGenerator) {t : ℕ} (s : St gen t)
    (hR : ∀ z ∈ s.R, z ∈ ordinary)
    (hdis : Disjoint (Iminus gen s) s.R) :
    (∀ z ∈ Rq gen s, z ∈ ordinary) ∧ Disjoint (Iminus gen s) (Rq gen s) := by
  classical
  cases hq : qv gen s with
  | none => simpa [Rq, hq] using And.intro hR hdis
  | some q =>
      by_cases hd : q ∈ core ∨ q ∈ Iminus gen s ∨ q ∈ s.R
      · simpa [Rq, hq, hd] using And.intro hR hdis
      · have hqo : q ∈ ordinary := by
          intro hc
          exact hd (Or.inl hc)
        constructor
        · intro z hz
          simp [Rq, hq, hd] at hz
          rcases hz with rfl | hz
          · exact hqo
          · exact hR z hz
        · rw [Finset.disjoint_left]
          intro z hzI hzR
          simp [Rq, hq, hd] at hzR
          rcases hzR with rfl | hzR
          · exact hd (Or.inr (Or.inl hzI))
          · exact (Finset.disjoint_left.mp hdis) hzI hzR

lemma Rnext_props (gen : FeedbackGenerator) {t : ℕ} (s : St gen t)
    (hR : ∀ z ∈ Rq gen s, z ∈ ordinary)
    (hdis : Disjoint (Iminus gen s) (Rq gen s)) :
    (∀ z ∈ Rnext gen s, z ∈ ordinary) ∧
      Disjoint (Iminus gen s) (Rnext gen s) := by
  classical
  by_cases hd : yv gen s ∈ core ∨ yv gen s ∈ Iminus gen s ∨ yv gen s ∈ Rq gen s
  · simpa [Rnext, hd] using And.intro hR hdis
  · constructor
    · intro z hz
      simp [Rnext, hd] at hz
      rcases hz with rfl | hz
      · intro hc
        exact hd (Or.inl hc)
      · exact hR z hz
    · rw [Finset.disjoint_left]
      intro z hzI hzR
      simp [Rnext, hd] at hzR
      rcases hzR with rfl | hzR
      · exact hd (Or.inr (Or.inl hzI))
      · exact (Finset.disjoint_left.mp hdis) hzI hzR

lemma state_inv (gen : FeedbackGenerator) (t : ℕ) :
    (∀ z ∈ (st gen t).I, z ∈ ordinary) ∧
    (∀ z ∈ (st gen t).R, z ∈ ordinary) ∧
    Disjoint (st gen t).I (st gen t).R := by
  induction t with
  | zero => simp [st, emptySt]
  | succ t ih =>
      rcases ih with ⟨hI, hR, hdis⟩
      have hIm := Iminus_props gen (st gen t) hI hdis
      have hRq := Rq_props gen (st gen t) hR hIm.2
      have hRn := Rnext_props gen (st gen t) hRq.1 hRq.2
      simpa [st, step] using And.intro hIm.1 (And.intro hRn.1 hRn.2)

lemma targetClass_uncountable : ¬ targetClass.Countable := by
  intro hc
  let f : Set ordinary → targetClass := fun A =>
    ⟨core ∪ ((fun z : ordinary => z.1) '' A),
      ⟨(fun z : ordinary => z.1) '' A,
        by rintro z ⟨w, hw, rfl⟩; exact w.2, rfl⟩⟩
  have hf : Function.Injective f := by
    intro A B h
    apply Set.ext
    intro z
    have hz := Set.ext_iff.mp (congrArg Subtype.val h) z.1
    have hnot : z.1 ∉ core := z.2
    change z.1 ∈ core ∪ ((fun w : ordinary => w.1) '' A) ↔
      z.1 ∈ core ∪ ((fun w : ordinary => w.1) '' B) at hz
    have himgA : z.1 ∈ (fun w : ordinary => w.1) '' A ↔ z ∈ A := by
      constructor
      · rintro ⟨w, hw, heq⟩
        simpa [Subtype.ext heq] using hw
      · intro hzA; exact ⟨z, hzA, rfl⟩
    have himgB : z.1 ∈ (fun w : ordinary => w.1) '' B ↔ z ∈ B := by
      constructor
      · rintro ⟨w, hw, heq⟩
        simpa [Subtype.ext heq] using hw
      · intro hzB; exact ⟨z, hzB, rfl⟩
    simpa [hnot, himgA, himgB] using hz
  letI : Infinite ordinary := ordinary_infinite.to_subtype
  letI : Countable targetClass := hc.to_subtype
  have hp : Countable (Set ordinary) := hf.countable
  exact GenLimit.UnionClosedness.powerSet_not_countable ordinary hp

lemma positive_claim : UniformlyGeneratableWithoutSamples := by
  refine ⟨fun t => 2 ^ t, pow_two_injective, 0, ?_⟩
  intro K hK t _
  obtain ⟨A, hA, rfl⟩ := hK
  exact Or.inl (core_mem t)

end Stage3Proof

open Stage3S2B
open Stage3Proof

theorem stage3_positive_checked :
    ¬ Stage3S2B.targetClass.Countable ∧
      Stage3S2B.UniformlyGeneratableWithoutSamples :=
  ⟨Stage3Proof.targetClass_uncountable, Stage3Proof.positive_claim⟩
