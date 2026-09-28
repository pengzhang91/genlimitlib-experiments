import Stage3Model

namespace Stage3Work

open Stage3S2B

structure RoundData where
  presentation : ℕ
  query : Option ℕ
  answer : Option Bool
  output : ℕ

noncomputable def ordinaryBlock (z : ℕ) : ℕ := by
  classical
  exact if z ∈ ordinary then z else 0

noncomputable def blocked {t : ℕ} (past : Fin t → RoundData) : Finset ℕ :=
  (Finset.univ.image fun i => (past i).presentation) ∪
  (Finset.univ.image fun i => ordinaryBlock ((past i).query.getD 0)) ∪
  (Finset.univ.image fun i => ordinaryBlock (past i).output)

noncomputable def nextPresentation {t : ℕ} (past : Fin t → RoundData) : ℕ :=
  Nat.find (Finset.exists_not_mem (blocked past))

noncomputable def makeRound (gen : FeedbackGenerator) (t : ℕ)
    (past : Fin t → RoundData) : RoundData := by
  let x := nextPresentation past
  let presentations : Fin (t + 1) → ℕ := Fin.lastCases x (fun i => (past i).presentation)
  let oldAnswers : Fin t → Option Bool := fun i => (past i).answer
  let q := gen.query t presentations oldAnswers
  let a : Option Bool := q.map fun z => membershipAnswer
    (core ∪ Set.range presentations) z
  let answers : Fin (t + 1) → Option Bool := Fin.lastCases a oldAnswers
  let y := gen.output t presentations answers
  exact ⟨x, q, a, y⟩

noncomputable def run (gen : FeedbackGenerator) (t : ℕ) : RoundData :=
  Nat.strongRecOn t fun t previous =>
    makeRound gen t (fun i => previous i i.isLt)

noncomputable def diagonalTranscript (gen : FeedbackGenerator) : Transcript where
  presentation t := (run gen t).presentation
  query t := (run gen t).query
  answer t := (run gen t).answer
  output t := (run gen t).output

private theorem run_eq_makeRound (gen : FeedbackGenerator) (t : ℕ) :
    run gen t = makeRound gen t (fun i => run gen i) := by
  rw [run, Nat.strongRecOn_eq]
  rfl

 theorem nextPresentation_not_blocked {t : ℕ} (past : Fin t → RoundData) :
    nextPresentation past ∉ blocked past := by
  exact Nat.find_spec (Finset.exists_not_mem (blocked past))

 theorem run_presentation_ne_prior (gen : FeedbackGenerator) (t : ℕ) (i : Fin t) :
    (run gen t).presentation ≠ (run gen i).presentation := by
  rw [run_eq_makeRound]
  change nextPresentation (fun i : Fin t => run gen i) ≠ (run gen i).presentation
  intro h
  have hn := nextPresentation_not_blocked (fun i : Fin t => run gen i)
  apply hn
  unfold blocked
  simp only [Finset.mem_union]
  exact Or.inl (Or.inl (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, h.symm⟩))

 theorem diagonal_presentation_injective (gen : FeedbackGenerator) :
    Function.Injective (diagonalTranscript gen).presentation := by
  intro i j hij
  by_contra hne
  rcases lt_or_gt_of_ne hne with hijlt | hjilt
  · exact run_presentation_ne_prior gen j ⟨i, hijlt⟩ hij.symm
  · exact run_presentation_ne_prior gen i ⟨j, hjilt⟩ hij

end Stage3Work

namespace Stage3Work

open Stage3S2B

private theorem exists_le_card_not_mem (s : Finset ℕ) :
    ∃ n, n ≤ s.card ∧ n ∉ s := by
  by_contra h
  push_neg at h
  have hsub : Finset.range (s.card + 1) ⊆ s := by
    intro n hn
    have hnlt : n < s.card + 1 := Finset.mem_range.mp hn
    have hnle : n ≤ s.card := by omega
    exact h n hnle
  have hcard := Finset.card_le_card hsub
  simp at hcard

 theorem blocked_card_le {t : ℕ} (past : Fin t → RoundData) :
    (blocked past).card ≤ 3 * t := by
  unfold blocked
  let X := Finset.univ.image fun i => (past i).presentation
  let Q := Finset.univ.image fun i => ordinaryBlock ((past i).query.getD 0)
  let Y := Finset.univ.image fun i => ordinaryBlock (past i).output
  have hX : X.card ≤ t := by
    dsimp [X]
    simpa using (Finset.card_image_le (s := (Finset.univ : Finset (Fin t))))
  have hQ : Q.card ≤ t := by
    dsimp [Q]
    simpa using (Finset.card_image_le (s := (Finset.univ : Finset (Fin t))))
  have hY : Y.card ≤ t := by
    dsimp [Y]
    simpa using (Finset.card_image_le (s := (Finset.univ : Finset (Fin t))))
  calc
    (X ∪ Q ∪ Y).card ≤ (X ∪ Q).card + Y.card := Finset.card_union_le _ _
    _ ≤ (X.card + Q.card) + Y.card := Nat.add_le_add_right (Finset.card_union_le _ _) _
    _ ≤ (t + t) + t := by omega
    _ = 3 * t := by omega

 theorem nextPresentation_le {t : ℕ} (past : Fin t → RoundData) :
    nextPresentation past ≤ 3 * t := by
  obtain ⟨n, hn, hnot⟩ := exists_le_card_not_mem (blocked past)
  calc
    nextPresentation past ≤ n := Nat.find_le hnot
    _ ≤ (blocked past).card := hn
    _ ≤ 3 * t := blocked_card_le past

 theorem diagonal_presentation_le (gen : FeedbackGenerator) (t : ℕ) :
    (diagonalTranscript gen).presentation t ≤ 3 * t := by
  change (run gen t).presentation ≤ 3 * t
  rw [run_eq_makeRound]
  exact nextPresentation_le (fun i : Fin t => run gen i)

 theorem diagonal_presentation_unbounded (gen : FeedbackGenerator) (c : ℕ) :
    ∃ t, c < (diagonalTranscript gen).presentation t := by
  by_contra h
  push_neg at h
  have hrange : Set.range (diagonalTranscript gen).presentation ⊆ Finset.range (c + 1) := by
    rintro z ⟨t, rfl⟩
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (h t))
  have hinfinite := Set.infinite_range_of_injective (diagonal_presentation_injective gen)
  exact hinfinite ((Finset.finite_toSet _).subset hrange)

private theorem ordinaryBlock_eq_self {z : ℕ} (hz : z ∈ ordinary) :
    ordinaryBlock z = z := by
  classical
  simp [ordinaryBlock, hz]

 theorem core_subset_diagonal_range (gen : FeedbackGenerator) :
    core ⊆ Set.range (diagonalTranscript gen).presentation := by
  intro z hz
  obtain ⟨t, ht⟩ := diagonal_presentation_unbounded gen z
  let s := Nat.find (diagonal_presentation_unbounded gen z)
  have hs : z < (diagonalTranscript gen).presentation s :=
    Nat.find_spec (diagonal_presentation_unbounded gen z)
  by_contra hnot
  have hnotPrior : ∀ i : Fin s, (run gen i).presentation ≠ z := by
    intro i hi
    apply hnot
    exact ⟨i, hi⟩
  have hnotBlocked : z ∉ blocked (fun i : Fin s => run gen i) := by
    intro hmem
    unfold blocked at hmem
    rcases Finset.mem_union.mp hmem with hxy | hy
    · rcases Finset.mem_union.mp hxy with hx | hq
      · rcases Finset.mem_image.mp hx with ⟨i, hi, hiz⟩
        exact hnotPrior i hiz
      · rcases Finset.mem_image.mp hq with ⟨i, hi, hiz⟩
        have hzero : z ≠ 0 := by
          rintro rfl
          rcases hz with ⟨k, hk⟩
          exact (pow_ne_zero k (by omega)) hk
        classical
        by_cases hordinary : (run gen i).query.getD 0 ∈ ordinary
        · have hqz : (run gen i).query.getD 0 = z :=
            (ordinaryBlock_eq_self hordinary).symm.trans hiz
          exact hordinary (hqz ▸ hz)
        · have hz0 : ordinaryBlock ((run gen i).query.getD 0) = 0 := by
            simp [ordinaryBlock, hordinary]
          exact hzero (hiz.symm.trans hz0)
    · rcases Finset.mem_image.mp hy with ⟨i, hi, hiz⟩
      have hzero : z ≠ 0 := by
        rintro rfl
        rcases hz with ⟨k, hk⟩
        exact (pow_ne_zero k (by omega)) hk
      classical
      by_cases hordinary : (run gen i).output ∈ ordinary
      · have hyz : (run gen i).output = z :=
          (ordinaryBlock_eq_self hordinary).symm.trans hiz
        exact hordinary (hyz ▸ hz)
      · have hz0 : ordinaryBlock (run gen i).output = 0 := by
          simp [ordinaryBlock, hordinary]
        exact hzero (hiz.symm.trans hz0)
  have hle : (diagonalTranscript gen).presentation s ≤ z := by
    change (run gen s).presentation ≤ z
    rw [run_eq_makeRound]
    exact Nat.find_le hnotBlocked
  omega

noncomputable def diagonalTarget (gen : FeedbackGenerator) : Language :=
  Set.range (diagonalTranscript gen).presentation

 theorem diagonalTarget_mem (gen : FeedbackGenerator) :
    diagonalTarget gen ∈ targetClass := by
  refine ⟨diagonalTarget gen ∩ ordinary, Set.inter_subset_right, ?_⟩
  apply Set.Subset.antisymm
  · intro z hz
    by_cases hc : z ∈ core
    · exact Or.inl hc
    · exact Or.inr ⟨hz, hc⟩
  · rintro z (hz | ⟨hz, ho⟩)
    · exact core_subset_diagonal_range gen hz
    · exact hz

 theorem diagonal_clean (gen : FeedbackGenerator) :
    Clean (diagonalTranscript gen).presentation (diagonalTarget gen) := by
  intro t
  exact ⟨t, rfl⟩

 theorem diagonal_complete (gen : FeedbackGenerator) :
    Complete (diagonalTranscript gen).presentation (diagonalTarget gen) := by
  rintro z ⟨t, rfl⟩
  exact ⟨t, rfl⟩

end Stage3Work

namespace Stage3Work

open Stage3S2B

 theorem run_presentation_eq (gen : FeedbackGenerator) (t : ℕ) :
    (run gen t).presentation = nextPresentation (fun i : Fin t => run gen i) := by
  rw [run_eq_makeRound]
  rfl

private theorem presentationHistory_eq (gen : FeedbackGenerator) (t : ℕ) :
    (Fin.lastCases (nextPresentation (fun i : Fin t => run gen i))
      (fun i => (run gen i).presentation)) =
    (fun i : Fin (t + 1) => (run gen i).presentation) := by
  funext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simpa using (run_presentation_eq gen t).symm
  · rw [Fin.lastCases_castSucc]
    simp only [Fin.coe_castSucc]

 theorem run_query_eq (gen : FeedbackGenerator) (t : ℕ) :
    (run gen t).query = gen.query t
      (fun i => (run gen i).presentation) (fun i => (run gen i).answer) := by
  rw [run_eq_makeRound]
  unfold makeRound
  dsimp
  rw [presentationHistory_eq]

 theorem run_answer_eq (gen : FeedbackGenerator) (t : ℕ) :
    (run gen t).answer = (run gen t).query.map fun z => membershipAnswer
      (core ∪ Set.range (fun i : Fin (t + 1) => (run gen i).presentation)) z := by
  rw [run_eq_makeRound]
  unfold makeRound
  dsimp
  rw [presentationHistory_eq]

private theorem answerHistory_eq (gen : FeedbackGenerator) (t : ℕ) :
    (Fin.lastCases ((run gen t).answer) (fun i => (run gen i).answer)) =
    (fun i : Fin (t + 1) => (run gen i).answer) := by
  funext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · rw [Fin.lastCases_last]
    simp only [Fin.val_last]
  · rw [Fin.lastCases_castSucc]
    simp only [Fin.coe_castSucc]

 theorem run_output_eq (gen : FeedbackGenerator) (t : ℕ) :
    (run gen t).output = gen.output t
      (fun i => (run gen i).presentation) (fun i => (run gen i).answer) := by
  rw [run_eq_makeRound]
  unfold makeRound
  dsimp
  rw [presentationHistory_eq]
  rw [← run_query_eq, ← run_answer_eq]
  rw [answerHistory_eq]

 theorem query_blocks_later_presentation (gen : FeedbackGenerator)
    {i s z : ℕ} (his : i < s) (hq : (run gen i).query = some z)
    (hz : z ∈ ordinary) : (run gen s).presentation ≠ z := by
  rw [run_eq_makeRound]
  change nextPresentation (fun j : Fin s => run gen j) ≠ z
  intro h
  have hn := nextPresentation_not_blocked (fun j : Fin s => run gen j)
  apply hn
  unfold blocked
  simp only [Finset.mem_union]
  apply Or.inl
  apply Or.inr
  apply Finset.mem_image.mpr
  refine ⟨⟨i, his⟩, Finset.mem_univ _, ?_⟩
  simp [hq, ordinaryBlock_eq_self hz, h]

 theorem output_blocks_later_presentation (gen : FeedbackGenerator)
    {i s z : ℕ} (his : i < s) (hy : (run gen i).output = z)
    (hz : z ∈ ordinary) : (run gen s).presentation ≠ z := by
  rw [run_eq_makeRound]
  change nextPresentation (fun j : Fin s => run gen j) ≠ z
  intro h
  have hn := nextPresentation_not_blocked (fun j : Fin s => run gen j)
  apply hn
  unfold blocked
  simp only [Finset.mem_union]
  apply Or.inr
  apply Finset.mem_image.mpr
  refine ⟨⟨i, his⟩, Finset.mem_univ _, ?_⟩
  simp [hy, ordinaryBlock_eq_self hz, h]

 theorem query_mem_target_iff (gen : FeedbackGenerator) (t z : ℕ)
    (hq : (run gen t).query = some z) :
    z ∈ diagonalTarget gen ↔
      z ∈ core ∪ Set.range (fun i : Fin (t + 1) => (run gen i).presentation) := by
  constructor
  · rintro ⟨s, hs⟩
    by_cases hst : s ≤ t
    · exact Or.inr ⟨⟨s, by omega⟩, hs⟩
    · by_cases hz : z ∈ core
      · exact Or.inl hz
      · exfalso
        have hord : z ∈ ordinary := hz
        exact query_blocks_later_presentation gen (by omega) hq hord hs
  · rintro (hz | ⟨i, hi⟩)
    · exact core_subset_diagonal_range gen hz
    · exact ⟨i, hi⟩

 theorem diagonal_follows_protocol (gen : FeedbackGenerator) :
    FollowsProtocol gen (diagonalTarget gen) (diagonalTranscript gen) := by
  intro t
  refine ⟨?_, ?_, ?_⟩
  · change (run gen t).query = gen.query t
      (fun i => (run gen i).presentation) (fun i => (run gen i).answer)
    exact run_query_eq gen t
  · change (run gen t).answer =
      match (run gen t).query with
      | none => none
      | some z => some (membershipAnswer (diagonalTarget gen) z)
    rw [run_answer_eq]
    cases hq : (run gen t).query with
    | none => simp
    | some z =>
        simp only [Option.map_some]
        congr 1
        unfold membershipAnswer
        classical
        congr 1
        exact propext (query_mem_target_iff gen t z hq).symm
  · change (run gen t).output = gen.output t
      (fun i => (run gen i).presentation) (fun i => (run gen i).answer)
    exact run_output_eq gen t

 theorem fresh_ordinary_output_not_mem_target (gen : FeedbackGenerator)
    {t z : ℕ} (hy : (diagonalTranscript gen).output t = z)
    (hfresh : z ∉ observedThrough (diagonalTranscript gen).presentation t)
    (hz : z ∈ ordinary) : z ∉ diagonalTarget gen := by
  rintro ⟨s, hs⟩
  by_cases hst : s ≤ t
  · apply hfresh
    exact ⟨s, hst, hs⟩
  · exact output_blocks_later_presentation gen (by omega) hy hz hs

end Stage3Work

namespace Stage3Work

open Stage3S2B

 theorem blocked_run_mono (gen : FeedbackGenerator) {i t : ℕ} (hit : i ≤ t) :
    blocked (fun j : Fin i => run gen j) ⊆
      blocked (fun j : Fin t => run gen j) := by
  intro z hz
  unfold blocked at hz ⊢
  rcases Finset.mem_union.mp hz with hxy | hy
  · rcases Finset.mem_union.mp hxy with hx | hq
    · rcases Finset.mem_image.mp hx with ⟨j, hj, rfl⟩
      apply Finset.mem_union_left
      apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨⟨j, lt_of_lt_of_le j.isLt hit⟩, Finset.mem_univ _, rfl⟩
    · rcases Finset.mem_image.mp hq with ⟨j, hj, rfl⟩
      apply Finset.mem_union_left
      apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨⟨j, lt_of_lt_of_le j.isLt hit⟩, Finset.mem_univ _, rfl⟩
  · rcases Finset.mem_image.mp hy with ⟨j, hj, rfl⟩
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨⟨j, lt_of_lt_of_le j.isLt hit⟩, Finset.mem_univ _, rfl⟩

 theorem diagonal_presentation_strictMono (gen : FeedbackGenerator) :
    StrictMono (diagonalTranscript gen).presentation := by
  intro i t hit
  have hnotT : (run gen t).presentation ∉ blocked (fun j : Fin t => run gen j) := by
    rw [run_presentation_eq]
    exact nextPresentation_not_blocked _
  have hnotI : (run gen t).presentation ∉ blocked (fun j : Fin i => run gen j) := by
    intro hmem
    exact hnotT (blocked_run_mono gen (Nat.le_of_lt hit) hmem)
  have hle : (run gen i).presentation ≤ (run gen t).presentation := by
    rw [run_presentation_eq]
    exact Nat.find_le hnotI
  have hne : (run gen t).presentation ≠ (run gen i).presentation := by
    simpa using run_presentation_ne_prior gen t ⟨i, hit⟩
  change (run gen i).presentation < (run gen t).presentation
  omega

noncomputable def diagonalOrdered (gen : FeedbackGenerator) : OrderedLanguage where
  carrier := diagonalTarget gen
  enumeration := (diagonalTranscript gen).presentation
  enumeration_injective := diagonal_presentation_injective gen
  range_enumeration := rfl

 theorem diagonalOrdered_ambient (gen : FeedbackGenerator) :
    InheritsAmbientOrder (diagonalOrdered gen) :=
  diagonal_presentation_strictMono gen

end Stage3Work
