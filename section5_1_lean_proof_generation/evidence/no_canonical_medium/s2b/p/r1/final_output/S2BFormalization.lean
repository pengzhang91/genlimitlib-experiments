import Stage3Model

open Set Filter
open scoped Topology

namespace Stage3Work

open Stage3S2B

lemma odd_not_core (n : ℕ) : 2 * n + 3 ∉ core := by
  rintro ⟨k, hk⟩
  have hodd : Odd (2 * n + 3) := ⟨n + 1, by omega⟩
  have hkpos : 0 < k := by
    by_contra h
    have : k = 0 := by omega
    subst k
    norm_num at hk
  have heven : Even (2 ^ k) := Nat.even_pow.mpr ⟨by simp, by omega⟩
  change 2 ^ k = 2 * n + 3 at hk
  rw [hk] at heven
  exact (Nat.not_even_iff_odd.mpr hodd) heven

lemma odd_injective : Function.Injective (fun n : ℕ => 2 * n + 3) := by
  intro a b h
  change 2 * a + 3 = 2 * b + 3 at h
  omega

lemma ordinary_infinite : ordinary.Infinite := by
  apply Set.Infinite.mono ?_ (Set.infinite_range_of_injective odd_injective)
  rintro z ⟨n, rfl⟩
  exact odd_not_core n

noncomputable def freshOrdinary (forbidden : Finset ℕ) : ℕ :=
  Classical.choose (ordinary_infinite.exists_not_mem_finset forbidden)

lemma freshOrdinary_mem (forbidden : Finset ℕ) : freshOrdinary forbidden ∈ ordinary :=
  (Classical.choose_spec (ordinary_infinite.exists_not_mem_finset forbidden)).1

lemma freshOrdinary_not_mem (forbidden : Finset ℕ) : freshOrdinary forbidden ∉ forbidden :=
  (Classical.choose_spec (ordinary_infinite.exists_not_mem_finset forbidden)).2

structure Row where
  presentation : ℕ
  query : Option ℕ
  answer : Option Bool
  output : ℕ

noncomputable def buildRow (gen : FeedbackGenerator) : (t : ℕ) → Row
  | t => by
      classical
      let previous : Fin t → Row := fun i => buildRow gen i
      let forbidden : Finset ℕ :=
        (Finset.univ.image fun i : Fin t => (previous i).presentation) ∪
        (Finset.univ.biUnion fun i : Fin t =>
          match (previous i).query with | none => ∅ | some z => {z}) ∪
        (Finset.univ.image fun i : Fin t => (previous i).output)
      let x := if Even t then 2 ^ (t / 2) else freshOrdinary forbidden
      let xs : Fin (t + 1) → ℕ := Fin.lastCases x (fun i => (previous i).presentation)
      let oldAnswers : Fin t → Option Bool := fun i => (previous i).answer
      let q := gen.query t xs oldAnswers
      let a := q.map fun z => decide (z ∈ core ∨ ∃ i : Fin (t + 1), xs i = z)
      let answers : Fin (t + 1) → Option Bool := Fin.lastCases a oldAnswers
      let y := gen.output t xs answers
      exact ⟨x, q, a, y⟩
termination_by t => t

noncomputable def builtTranscript (gen : FeedbackGenerator) : Transcript where
  presentation t := (buildRow gen t).presentation
  query t := (buildRow gen t).query
  answer t := (buildRow gen t).answer
  output t := (buildRow gen t).output

noncomputable def builtTarget (gen : FeedbackGenerator) : Language :=
  Set.range (builtTranscript gen).presentation


lemma build_presentation_even (gen : FeedbackGenerator) (t : ℕ) (ht : Even t) :
    (buildRow gen t).presentation = 2 ^ (t / 2) := by
  rw [buildRow.eq_1]
  simp [ht]

lemma build_presentation_odd (gen : FeedbackGenerator) (t : ℕ) (ht : ¬ Even t) :
    (buildRow gen t).presentation = freshOrdinary
      ((Finset.univ.image fun i : Fin t => (buildRow gen i).presentation) ∪
       (Finset.univ.biUnion fun i : Fin t =>
          match (buildRow gen i).query with | none => ∅ | some z => {z}) ∪
       (Finset.univ.image fun i : Fin t => (buildRow gen i).output)) := by
  rw [buildRow.eq_1]
  simp [ht]

lemma odd_presentation_mem_ordinary (gen : FeedbackGenerator) (t : ℕ) (ht : ¬ Even t) :
    (builtTranscript gen).presentation t ∈ ordinary := by
  change (buildRow gen t).presentation ∈ ordinary
  rw [build_presentation_odd gen t ht]
  exact freshOrdinary_mem _

lemma odd_presentation_ne_prior_presentation (gen : FeedbackGenerator) (t : ℕ)
    (ht : ¬ Even t) (i : ℕ) (hi : i < t) :
    (builtTranscript gen).presentation t ≠ (builtTranscript gen).presentation i := by
  change (buildRow gen t).presentation ≠ (buildRow gen i).presentation
  rw [build_presentation_odd gen t ht]
  intro h
  have hm : (buildRow gen i).presentation ∈
      ((Finset.univ.image fun j : Fin t => (buildRow gen j).presentation) ∪
       (Finset.univ.biUnion fun j : Fin t =>
          match (buildRow gen j).query with | none => ∅ | some z => {z}) ∪
       (Finset.univ.image fun j : Fin t => (buildRow gen j).output)) := by
    apply Finset.mem_union_left
    apply Finset.mem_union_left
    exact Finset.mem_image.mpr ⟨⟨i, hi⟩, Finset.mem_univ _, rfl⟩
  exact freshOrdinary_not_mem _ (h ▸ hm)

lemma odd_presentation_ne_prior_output (gen : FeedbackGenerator) (t : ℕ)
    (ht : ¬ Even t) (i : ℕ) (hi : i < t) :
    (builtTranscript gen).presentation t ≠ (builtTranscript gen).output i := by
  change (buildRow gen t).presentation ≠ (buildRow gen i).output
  rw [build_presentation_odd gen t ht]
  intro h
  have hm : (buildRow gen i).output ∈
      ((Finset.univ.image fun j : Fin t => (buildRow gen j).presentation) ∪
       (Finset.univ.biUnion fun j : Fin t =>
          match (buildRow gen j).query with | none => ∅ | some z => {z}) ∪
       (Finset.univ.image fun j : Fin t => (buildRow gen j).output)) := by
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨⟨i, hi⟩, Finset.mem_univ _, rfl⟩
  exact freshOrdinary_not_mem _ (h ▸ hm)

lemma odd_presentation_ne_prior_query (gen : FeedbackGenerator) (t : ℕ)
    (ht : ¬ Even t) (i : ℕ) (hi : i < t) (z : ℕ)
    (hq : (builtTranscript gen).query i = some z) :
    (builtTranscript gen).presentation t ≠ z := by
  change (buildRow gen t).presentation ≠ z
  rw [build_presentation_odd gen t ht]
  intro h
  have hm : z ∈
      ((Finset.univ.image fun j : Fin t => (buildRow gen j).presentation) ∪
       (Finset.univ.biUnion fun j : Fin t =>
          match (buildRow gen j).query with | none => ∅ | some w => {w}) ∪
       (Finset.univ.image fun j : Fin t => (buildRow gen j).output)) := by
    apply Finset.mem_union_left
    apply Finset.mem_union_right
    refine Finset.mem_biUnion.mpr ⟨⟨i, hi⟩, Finset.mem_univ _, ?_⟩
    change (buildRow gen i).query = some z at hq
    simp [hq]
  exact freshOrdinary_not_mem _ (h ▸ hm)

lemma core_presented (gen : FeedbackGenerator) (k : ℕ) :
    (builtTranscript gen).presentation (k + k) = 2 ^ k := by
  change (buildRow gen (k + k)).presentation = 2 ^ k
  rw [build_presentation_even gen (k + k) ⟨k, rfl⟩]
  congr
  omega

lemma built_presentation_injective (gen : FeedbackGenerator) :
    Function.Injective (builtTranscript gen).presentation := by
  intro a b hab
  rcases le_total a b with hab' | hba
  · rcases eq_or_lt_of_le hab' with rfl | hlt
    · rfl
    exfalso
    by_cases hb : Even b
    · rcases hb with ⟨k, rfl⟩
      have haodd : ¬ Even a := by
        intro ha
        rcases ha with ⟨j, rfl⟩
        rw [core_presented gen j, core_presented gen k] at hab
        have := Nat.pow_right_injective (by norm_num : 2 ≤ (2 : ℕ)) hab
        omega
      have hord := odd_presentation_mem_ordinary gen a haodd
      have hcore : (builtTranscript gen).presentation (k + k) ∈ core := by
        rw [core_presented]
        exact ⟨k, rfl⟩
      rw [hab] at hord
      exact hord hcore
    · exact odd_presentation_ne_prior_presentation gen b hb a hlt hab.symm
  · rcases eq_or_lt_of_le hba with rfl | hlt
    · rfl
    exfalso
    exact (odd_presentation_ne_prior_presentation gen a (by
      intro ha
      rcases ha with ⟨k, rfl⟩
      by_cases hb : Even b
      · rcases hb with ⟨j, rfl⟩
        rw [core_presented gen k, core_presented gen j] at hab
        have := Nat.pow_right_injective (by norm_num : 2 ≤ (2 : ℕ)) hab
        omega
      · have hord := odd_presentation_mem_ordinary gen b hb
        have hcore : (builtTranscript gen).presentation (k + k) ∈ core := by
            rw [core_presented]; exact ⟨k, rfl⟩
        rw [← hab] at hord
        exact hord hcore) b hlt) hab

lemma builtTarget_mem_class (gen : FeedbackGenerator) : builtTarget gen ∈ targetClass := by
  refine ⟨builtTarget gen ∩ ordinary, inter_subset_right, ?_⟩
  apply Set.Subset.antisymm
  · intro z hz
    by_cases hc : z ∈ core
    · exact Or.inl hc
    · exact Or.inr ⟨hz, hc⟩
  · rintro z (hc | ⟨hz, _⟩)
    · rcases hc with ⟨k, rfl⟩
      exact ⟨k + k, core_presented gen k⟩
    · exact hz

lemma built_clean (gen : FeedbackGenerator) :
    Clean (builtTranscript gen).presentation (builtTarget gen) := by
  intro t
  exact ⟨t, rfl⟩

lemma built_complete (gen : FeedbackGenerator) :
    Complete (builtTranscript gen).presentation (builtTarget gen) := by
  rintro z ⟨t, rfl⟩
  exact ⟨t, rfl⟩


lemma even_presentation_mem_core (gen : FeedbackGenerator) (t : ℕ) (ht : Even t) :
    (builtTranscript gen).presentation t ∈ core := by
  rcases ht with ⟨k, rfl⟩
  rw [core_presented]
  exact ⟨k, rfl⟩

lemma query_target_iff (gen : FeedbackGenerator) (t z : ℕ)
    (hq : (builtTranscript gen).query t = some z) :
    z ∈ builtTarget gen ↔ z ∈ core ∨
      ∃ i : Fin (t + 1), (builtTranscript gen).presentation i = z := by
  constructor
  · rintro ⟨s, hs⟩
    by_cases hc : z ∈ core
    · exact Or.inl hc
    right
    by_cases hst : s ≤ t
    · exact ⟨⟨s, by omega⟩, hs⟩
    · have hsodd : ¬ Even s := by
        intro hseven
        exact hc (hs ▸ even_presentation_mem_core gen s hseven)
      exact False.elim (odd_presentation_ne_prior_query gen s hsodd t (by omega) z hq hs)
  · rintro (hc | ⟨i, hi⟩)
    · rcases hc with ⟨k, rfl⟩
      exact ⟨k + k, core_presented gen k⟩
    · exact ⟨i, hi⟩

noncomputable def builtPresenter (gen : FeedbackGenerator) : CausalPresenter where
  next t _ _ _ _ := (builtTranscript gen).presentation t

lemma built_presented_by (gen : FeedbackGenerator) :
    PresentedBy (builtPresenter gen) (builtTranscript gen) := by
  intro t
  rfl

-- First two conjuncts are independent of the diagonal transcript.
lemma uniform_generation : UniformlyGeneratableWithoutSamples := by
  refine ⟨fun k => 2 ^ k, ?_, 0, ?_⟩
  · intro a b h
    exact Nat.pow_right_injective (by norm_num : 2 ≤ (2 : ℕ)) h
  · intro K hK t _
    rcases hK with ⟨A, hA, rfl⟩
    exact Or.inl ⟨t, rfl⟩

lemma targetClass_uncountable : ¬ targetClass.Countable := by
  intro hcount
  classical
  let encodeOrd : Set ℕ → Language := fun B => (fun n => 2 * n + 3) '' B
  let encodeTarget : Set ℕ → Language := fun B => core ∪ encodeOrd B
  have hmem : ∀ B, encodeTarget B ∈ targetClass := by
    intro B
    refine ⟨encodeOrd B, ?_, rfl⟩
    rintro z ⟨n, hn, rfl⟩
    exact odd_not_core n
  let intoClass : Set ℕ → targetClass := fun B => ⟨encodeTarget B, hmem B⟩
  have hinto : Function.Injective intoClass := by
    intro A B hab
    apply Set.ext
    intro n
    have hs : 2 * n + 3 ∈ encodeTarget A ↔ 2 * n + 3 ∈ encodeTarget B := by
      simpa [intoClass] using Set.ext_iff.mp (congrArg Subtype.val hab) (2 * n + 3)
    simpa [encodeTarget, encodeOrd, odd_not_core, odd_injective.eq_iff] using hs
  rcases Set.countable_iff_exists_injective.mp hcount with ⟨code, hcode⟩
  let F : Set ℕ → ℕ := fun B => code (intoClass B)
  have hF : Function.Injective F := hcode.comp hinto
  exact Function.cantor_injective F hF

end Stage3Work

open Stage3S2B
open Stage3Work


/-- Checked positive portion of `Stage3S2B.MainClaim`. -/
theorem stage3_positive :
    ¬ Stage3S2B.targetClass.Countable ∧
      Stage3S2B.UniformlyGeneratableWithoutSamples := by
  exact ⟨targetClass_uncountable, uniform_generation⟩
