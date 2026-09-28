import Stage3Model
import GenLimit.Paper10_UnionClosednessOfLanguageGeneration.Cardinality

open Set Filter

namespace Stage3S2B

private def encodeOrdinary (A : Set {n // n ∈ ordinary}) : Language :=
  core ∪ {n | ∃ h : n ∈ ordinary, (⟨n, h⟩ : {n // n ∈ ordinary}) ∈ A}

private theorem encodeOrdinary_mem (A : Set {n // n ∈ ordinary}) :
    encodeOrdinary A ∈ targetClass := by
  refine ⟨{n | ∃ h : n ∈ ordinary, (⟨n, h⟩ : {n // n ∈ ordinary}) ∈ A}, ?_, rfl⟩
  intro n hn
  exact hn.choose

private theorem encodeOrdinary_injective : Function.Injective encodeOrdinary := by
  intro A B h
  ext n
  have hn : (n : ℕ) ∈ ordinary := n.property
  have hnot : (n : ℕ) ∉ core := hn
  have heq : (n : ℕ) ∈ encodeOrdinary A ↔ (n : ℕ) ∈ encodeOrdinary B := by rw [h]
  simpa [encodeOrdinary, hnot] using heq

private theorem ordinary_infinite : Infinite {n // n ∈ ordinary} := by
  let f : ℕ → {n // n ∈ ordinary} := fun n =>
    ⟨2 * n + 3, by
      intro h
      obtain ⟨k, hk⟩ := h
      change 2 ^ k = 2 * n + 3 at hk
      have hodd : Odd (2 * n + 3) := ⟨n + 1, by omega⟩
      by_cases hk0 : k = 0
      · subst k
        simp at hk
      · have heven : Even (2 ^ k) := Nat.even_pow.mpr ⟨even_two, hk0⟩
        rw [hk] at heven
        exact (Nat.not_even_iff_odd.mpr hodd) heven⟩
  exact Infinite.of_injective f (by
    intro a b h
    simp only [f, Subtype.mk.injEq] at h
    omega)

private theorem targetClass_not_countable : ¬ targetClass.Countable := by
  intro hcount
  have henc : Set.range encodeOrdinary ⊆ targetClass := by
    rintro _ ⟨A, rfl⟩
    exact encodeOrdinary_mem A
  have hrange : (Set.range encodeOrdinary).Countable := hcount.mono henc
  haveI : Countable (Set.range encodeOrdinary) := hrange.to_subtype
  have hdomain : Countable (Set {n // n ∈ ordinary}) :=
    (show Function.Injective (fun A =>
      (⟨encodeOrdinary A, ⟨A, rfl⟩⟩ : Set.range encodeOrdinary)) from by
        intro A B h
        exact encodeOrdinary_injective (Subtype.mk.inj h)).countable
  letI : Infinite {n // n ∈ ordinary} := ordinary_infinite
  exact GenLimit.UnionClosedness.powerSet_not_countable {n // n ∈ ordinary} hdomain

private theorem uniform_generation : UniformlyGeneratableWithoutSamples := by
  refine ⟨fun t => 2 ^ t, ?_, 0, ?_⟩
  · exact Nat.pow_right_injective (by omega)
  · intro K hK t _
    obtain ⟨A, hA, rfl⟩ := hK
    exact Or.inl ⟨t, rfl⟩


private def oddCandidate (j : ℕ) : ℕ := 2 * j + 3

private theorem oddCandidate_injective : Function.Injective oddCandidate := by
  intro a b h
  simp only [oddCandidate] at h
  omega

private theorem oddCandidate_ordinary (j : ℕ) : oddCandidate j ∈ ordinary := by
  intro h
  obtain ⟨k, hk⟩ := h
  change 2 ^ k = 2 * j + 3 at hk
  have hodd : Odd (2 * j + 3) := ⟨j + 1, by omega⟩
  by_cases hk0 : k = 0
  · subst k
    simp at hk
  · have heven : Even (2 ^ k) := Nat.even_pow.mpr ⟨even_two, hk0⟩
    rw [hk] at heven
    exact (Nat.not_even_iff_odd.mpr hodd) heven

private noncomputable def freshIndex (S : Finset ℕ) : ℕ := by
  classical
  exact Nat.find (Infinite.exists_not_mem_finset (S.preimage oddCandidate oddCandidate_injective.injOn))

private theorem freshIndex_spec (S : Finset ℕ) : oddCandidate (freshIndex S) ∉ S := by
  classical
  let h := Infinite.exists_not_mem_finset (S.preimage oddCandidate oddCandidate_injective.injOn)
  simpa [freshIndex] using Nat.find_spec h


private theorem freshIndex_le_card (S : Finset ℕ) : freshIndex S ≤ S.card := by
  classical
  let H := Infinite.exists_not_mem_finset (S.preimage oddCandidate oddCandidate_injective.injOn)
  change Nat.find H ≤ S.card
  by_contra hle
  have hcardlt : S.card < Nat.find H := Nat.lt_of_not_ge hle
  have hsub : (Finset.range (Nat.find H)).image oddCandidate ⊆ S := by
    intro z hz
    simp only [Finset.mem_image, Finset.mem_range] at hz
    obtain ⟨i, hi, rfl⟩ := hz
    have hnot := Nat.find_min H hi
    simp only [Finset.mem_preimage, not_not] at hnot
    exact hnot
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ oddCandidate_injective, Finset.card_range] at hc
  omega

private structure BuildState (t : ℕ) where
  presentation : Fin t → ℕ
  query : Fin t → Option ℕ
  answer : Fin t → Option Bool
  output : Fin t → ℕ
  admitted : Finset ℕ
  rejected : Finset ℕ

private def extendFin {α : Type} {t : ℕ} (f : Fin t → α) (x : α) : Fin (t + 1) → α :=
  Fin.lastCases x f

private noncomputable def step (gen : FeedbackGenerator) (t : ℕ)
    (s : BuildState t) : BuildState (t + 1) := by
  classical
  let isEven := t % 2 = 0
  let x := if isEven then 2 ^ (t / 2)
    else oddCandidate (freshIndex (s.admitted ∪ s.rejected))
  let admitted' := if isEven then s.admitted else insert x s.admitted
  let xs := extendFin s.presentation x
  let q := gen.query t xs s.answer
  let b : Option Bool := q.map fun z => membershipAnswer (core ∪ (↑admitted' : Set ℕ)) z
  let rejected' := match q with
    | none => s.rejected
    | some z => insert z s.rejected
  let answers := extendFin s.answer b
  let y := gen.output t xs answers
  let rejected'' := insert y rejected'
  exact {
    presentation := xs
    query := extendFin s.query q
    answer := answers
    output := extendFin s.output y
    admitted := admitted'
    rejected := rejected'' }

private noncomputable def build (gen : FeedbackGenerator) : (t : ℕ) → BuildState t
  | 0 => {
      presentation := Fin.elim0
      query := Fin.elim0
      answer := Fin.elim0
      output := Fin.elim0
      admitted := ∅
      rejected := ∅ }
  | t + 1 => step gen t (build gen t)

private noncomputable def builtTranscript (gen : FeedbackGenerator) : Transcript where
  presentation t := (build gen (t + 1)).presentation (Fin.last t)
  query t := (build gen (t + 1)).query (Fin.last t)
  answer t := (build gen (t + 1)).answer (Fin.last t)
  output t := (build gen (t + 1)).output (Fin.last t)

private def admittedLimit (gen : FeedbackGenerator) : Language :=
  {z | ∃ t, z ∈ (build gen t).admitted}

private def builtTarget (gen : FeedbackGenerator) : Language := core ∪ admittedLimit gen

private noncomputable def builtPresenter (gen : FeedbackGenerator) : CausalPresenter where
  next t _ _ _ _ := (builtTranscript gen).presentation t

private theorem build_succ_old (gen : FeedbackGenerator) (t : ℕ) :
    ∀ i : Fin t,
      (build gen (t + 1)).presentation i.castSucc = (build gen t).presentation i ∧
      (build gen (t + 1)).query i.castSucc = (build gen t).query i ∧
      (build gen (t + 1)).answer i.castSucc = (build gen t).answer i ∧
      (build gen (t + 1)).output i.castSucc = (build gen t).output i := by
  intro i
  simp [build, step, extendFin]

private theorem build_prefix (gen : FeedbackGenerator) {s t : ℕ} (h : s < t) :
    (build gen t).presentation ⟨s, h⟩ = (builtTranscript gen).presentation s := by
  induction t with
  | zero => omega
  | succ t ih =>
      by_cases hst : s = t
      · subst s
        have hi : (⟨t, h⟩ : Fin (t + 1)) = Fin.last t := Fin.ext (by simp)
        rw [hi]
        simp [builtTranscript, build, step, extendFin]
      · have hs : s < t := by omega
        have hi : (⟨s, h⟩ : Fin (t + 1)) = (⟨s, hs⟩ : Fin t).castSucc := Fin.ext rfl
        rw [hi, (build_succ_old gen t ⟨s, hs⟩).1]
        exact ih hs


private theorem build_good (gen : FeedbackGenerator) : ∀ t,
    (∀ z ∈ (build gen t).admitted, z ∈ ordinary) ∧
    (build gen t).admitted.card ≤ t ∧
    (build gen t).rejected.card ≤ 2 * t := by
  intro t
  induction t with
  | zero => simp [build]
  | succ t ih =>
      classical
      rw [build]
      unfold step
      dsimp only
      split_ifs with heven
      · constructor
        · exact ih.1
        constructor
        · exact ih.2.1.trans (Nat.le_succ t)
        · dsimp only
          split
          · calc
              (insert _ (build gen t).rejected).card ≤ (build gen t).rejected.card + 1 :=
                Finset.card_insert_le _ _
              _ ≤ 2 * t + 1 := Nat.add_le_add_right ih.2.2 1
              _ ≤ 2 * (t + 1) := by omega
          · calc
              (insert _ (insert _ (build gen t).rejected)).card ≤
                  (insert _ (build gen t).rejected).card + 1 := Finset.card_insert_le _ _
              _ ≤ ((build gen t).rejected.card + 1) + 1 :=
                Nat.add_le_add_right (Finset.card_insert_le _ _) 1
              _ ≤ (2 * t + 1) + 1 :=
                Nat.add_le_add_right (Nat.add_le_add_right ih.2.2 1) 1
              _ = 2 * (t + 1) := by omega
      · constructor
        · intro z hz
          simp only [Finset.mem_insert] at hz
          rcases hz with rfl | hz
          · exact oddCandidate_ordinary _
          · exact ih.1 z hz
        constructor
        · exact (Finset.card_insert_le _ _).trans (by omega)
        · dsimp only
          split
          · calc
              (insert _ (build gen t).rejected).card ≤ (build gen t).rejected.card + 1 :=
                Finset.card_insert_le _ _
              _ ≤ 2 * t + 1 := Nat.add_le_add_right ih.2.2 1
              _ ≤ 2 * (t + 1) := by omega
          · calc
              (insert _ (insert _ (build gen t).rejected)).card ≤
                  (insert _ (build gen t).rejected).card + 1 := Finset.card_insert_le _ _
              _ ≤ ((build gen t).rejected.card + 1) + 1 :=
                Nat.add_le_add_right (Finset.card_insert_le _ _) 1
              _ ≤ (2 * t + 1) + 1 :=
                Nat.add_le_add_right (Nat.add_le_add_right ih.2.2 1) 1
              _ = 2 * (t + 1) := by omega

end Stage3S2B


theorem stage3_positive :
    ¬ Stage3S2B.targetClass.Countable ∧
      Stage3S2B.UniformlyGeneratableWithoutSamples := by
  exact ⟨Stage3S2B.targetClass_not_countable, Stage3S2B.uniform_generation⟩
