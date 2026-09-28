import Stage3Model

open Set

namespace Stage3Work
open Stage3S2B

structure Round where
  x : ℕ
  q : Option ℕ
  a : Option Bool
  y : ℕ

private theorem ordinary_infinite : ordinary.Infinite := by
  apply (Set.infinite_range_of_injective (show Function.Injective (fun n : ℕ => 2*n+3) by
    intro a b h
    dsimp at h
    omega)).mono
  rintro z ⟨n, rfl⟩ hcore
  rcases hcore with ⟨k, hk⟩
  cases k with
  | zero => simp at hk
  | succ k =>
      change 2 ^ (k+1) = 2*n+3 at hk
      rw [pow_succ] at hk
      omega

private noncomputable def chooseOrdinary
    (prior : Finset ℕ) : ℕ := by
  classical
  exact Nat.find (ordinary_infinite.exists_not_mem_finset prior)

private theorem chooseOrdinary_mem (prior : Finset ℕ) :
    chooseOrdinary prior ∈ ordinary := by
  classical
  exact (Nat.find_spec (ordinary_infinite.exists_not_mem_finset prior)).1

private theorem chooseOrdinary_not_mem (prior : Finset ℕ) :
    chooseOrdinary prior ∉ prior := by
  classical
  exact (Nat.find_spec (ordinary_infinite.exists_not_mem_finset prior)).2

private def priorValues (r : Fin t → Round) : Finset ℕ :=
  (Finset.univ.image fun i => (r i).x) ∪
  (Finset.univ.image fun i => (r i).q.getD 0) ∪
  (Finset.univ.image fun i => (r i).y)

private noncomputable def localAnswer
    (t : ℕ) (r : Fin t → Round) (x z : ℕ) : Bool := by
  classical
  exact decide (z ∈ core ∨ z = x ∨ ∃ i, (r i).x = z)

private noncomputable def nextRound (gen : FeedbackGenerator)
    (t : ℕ) (r : Fin t → Round) : Round := by
  classical
  let x := if Even t then 2 ^ (t / 2) else chooseOrdinary (priorValues r)
  let xs : Fin (t+1) → ℕ := Fin.lastCases x (fun i => (r i).x)
  let oldAnswers : Fin t → Option Bool := fun i => (r i).a
  let q := gen.query t xs oldAnswers
  let a := match q with
    | none => none
    | some z => some (localAnswer t r x z)
  let answers : Fin (t+1) → Option Bool := Fin.lastCases a oldAnswers
  let y := gen.output t xs answers
  exact ⟨x, q, a, y⟩

private noncomputable def rounds (gen : FeedbackGenerator) : ℕ → Round
  | 0 => nextRound gen 0 Fin.elim0
  | t+1 => nextRound gen (t+1) (fun i => rounds gen i)

private theorem rounds_eq_next (gen : FeedbackGenerator) (t : ℕ) :
    rounds gen t = nextRound gen t (fun i => rounds gen i) := by
  cases t with
  | zero =>
      rw [rounds]
      congr
      funext i
      exact Fin.elim0 i
  | succ t =>
      rw [rounds]

noncomputable def diagonalTranscript (gen : FeedbackGenerator) : Transcript where
  presentation t := (rounds gen t).x
  query t := (rounds gen t).q
  answer t := (rounds gen t).a
  output t := (rounds gen t).y

noncomputable def diagonalTarget (gen : FeedbackGenerator) : Language :=
  Set.range (diagonalTranscript gen).presentation

end Stage3Work

namespace Stage3Work
open Stage3S2B

private theorem round_x_of_even (gen : FeedbackGenerator) (t : ℕ) (ht : Even t) :
    (rounds gen t).x = 2 ^ (t / 2) := by
  rw [rounds_eq_next]
  simp [nextRound, ht]

private theorem round_x_of_not_even (gen : FeedbackGenerator) (t : ℕ) (ht : ¬ Even t) :
    (rounds gen t).x = chooseOrdinary (priorValues (fun i : Fin t => rounds gen i)) := by
  rw [rounds_eq_next]
  simp [nextRound, ht]

private theorem round_x_ordinary_of_not_even (gen : FeedbackGenerator) (t : ℕ)
    (ht : ¬ Even t) : (rounds gen t).x ∈ ordinary := by
  rw [round_x_of_not_even gen t ht]
  exact chooseOrdinary_mem _

private theorem round_x_ne_prior_x_of_not_even (gen : FeedbackGenerator) (t : ℕ)
    (ht : ¬ Even t) (i : Fin t) : (rounds gen t).x ≠ (rounds gen i).x := by
  rw [round_x_of_not_even gen t ht]
  intro h
  have hnot := chooseOrdinary_not_mem (priorValues (fun i : Fin t => rounds gen i))
  apply hnot
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, h.symm⟩

private theorem round_x_ne_prior_y_of_not_even (gen : FeedbackGenerator) (t : ℕ)
    (ht : ¬ Even t) (i : Fin t) : (rounds gen t).x ≠ (rounds gen i).y := by
  rw [round_x_of_not_even gen t ht]
  intro h
  have hnot := chooseOrdinary_not_mem (priorValues (fun i : Fin t => rounds gen i))
  apply hnot
  apply Finset.mem_union_right
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, h.symm⟩

private theorem core_subset_target (gen : FeedbackGenerator) :
    core ⊆ diagonalTarget gen := by
  rintro z ⟨k, rfl⟩
  refine ⟨2*k, ?_⟩
  change (rounds gen (2*k)).x = 2^k
  rw [round_x_of_even gen (2*k) (even_two_mul k)]
  congr
  omega

private theorem diagonalTarget_mem_class (gen : FeedbackGenerator) :
    diagonalTarget gen ∈ targetClass := by
  refine ⟨diagonalTarget gen \ core, Set.diff_subset_compl _ _, ?_⟩
  ext z
  constructor
  · intro hz
    by_cases hc : z ∈ core
    · exact Or.inl hc
    · exact Or.inr ⟨hz, hc⟩
  · rintro (hc | ⟨hz, _⟩)
    · exact core_subset_target gen hc
    · exact hz

private theorem presentation_injective (gen : FeedbackGenerator) :
    Function.Injective (diagonalTranscript gen).presentation := by
  intro i j hij
  change (rounds gen i).x = (rounds gen j).x at hij
  rcases lt_trichotomy i j with hlt | rfl | hgt
  · by_cases hj : Even j
    · have hjcore : (rounds gen j).x ∈ core := by
        rw [round_x_of_even gen j hj]
        exact ⟨j/2, rfl⟩
      by_cases hi : Even i
      · rw [round_x_of_even gen i hi, round_x_of_even gen j hj] at hij
        have he := Nat.pow_right_injective (by omega) hij
        have hi2 : i / 2 * 2 = i := Nat.div_mul_cancel (even_iff_two_dvd.mp hi)
        have hj2 : j / 2 * 2 = j := Nat.div_mul_cancel (even_iff_two_dvd.mp hj)
        omega
      · have hiord := round_x_ordinary_of_not_even gen i hi
        exact False.elim (hiord (hij ▸ hjcore))
    · exact False.elim (round_x_ne_prior_x_of_not_even gen j hj ⟨i, hlt⟩ hij.symm)
  · rfl
  · by_cases hi : Even i
    · have hicore : (rounds gen i).x ∈ core := by
        rw [round_x_of_even gen i hi]
        exact ⟨i/2, rfl⟩
      by_cases hj : Even j
      · rw [round_x_of_even gen i hi, round_x_of_even gen j hj] at hij
        have he := Nat.pow_right_injective (by omega) hij
        have hi2 : i / 2 * 2 = i := Nat.div_mul_cancel (even_iff_two_dvd.mp hi)
        have hj2 : j / 2 * 2 = j := Nat.div_mul_cancel (even_iff_two_dvd.mp hj)
        omega
      · have hjord := round_x_ordinary_of_not_even gen j hj
        exact False.elim (hjord (hij.symm ▸ hicore))
    · exact False.elim (round_x_ne_prior_x_of_not_even gen i hi ⟨j, hgt⟩ hij)

end Stage3Work

namespace Stage3Work
open Stage3S2B

private theorem round_x_ne_prior_q_of_not_even (gen : FeedbackGenerator) (t : ℕ)
    (ht : ¬ Even t) (i : Fin t) (z : ℕ) (hq : (rounds gen i).q = some z) :
    (rounds gen t).x ≠ z := by
  rw [round_x_of_not_even gen t ht]
  intro h
  have hnot := chooseOrdinary_not_mem (priorValues (fun i : Fin t => rounds gen i))
  apply hnot
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  refine Finset.mem_image.mpr ⟨i, Finset.mem_univ _, ?_⟩
  simp [hq, h]

private theorem round_x_formula (gen : FeedbackGenerator) (t : ℕ) :
    (rounds gen t).x =
      (if Even t then 2 ^ (t / 2)
       else chooseOrdinary (priorValues (fun i : Fin t => rounds gen i))) := by
  rw [rounds_eq_next]
  rfl


private theorem rounds_castSucc (gen : FeedbackGenerator) {t : ℕ} (i : Fin t) :
    rounds gen i.castSucc = rounds gen i := by
  apply congrArg (rounds gen)
  rfl

private theorem rounds_last (gen : FeedbackGenerator) (t : ℕ) :
    rounds gen (Fin.last t) = rounds gen t := by
  apply congrArg (rounds gen)
  rfl

private theorem query_projection (gen : FeedbackGenerator) (t : ℕ) :
    (rounds gen t).q = gen.query t
      (fun i => (rounds gen i).x) (fun i => (rounds gen i).a) := by
  rw [rounds_eq_next]
  unfold nextRound
  dsimp only
  congr 1
  funext i
  refine Fin.lastCases ?_ (fun j => by rw [Fin.lastCases_castSucc, rounds_castSucc]) i
  rw [Fin.lastCases_last, rounds_last]
  exact (round_x_formula gen t).symm

private theorem answer_raw_projection (gen : FeedbackGenerator) (t : ℕ) :
    (rounds gen t).a = match (rounds gen t).q with
      | none => none
      | some z => some (localAnswer t (fun i => rounds gen i)
          (rounds gen t).x z) := by
  rw [rounds_eq_next]
  unfold nextRound
  dsimp only

private theorem output_projection (gen : FeedbackGenerator) (t : ℕ) :
    (rounds gen t).y = gen.output t
      (fun i => (rounds gen i).x) (fun i => (rounds gen i).a) := by
  rw [rounds_eq_next]
  unfold nextRound
  dsimp only
  have hx : (fun i : Fin (t+1) =>
      Fin.lastCases
        (if Even t then 2 ^ (t / 2)
         else chooseOrdinary (priorValues (fun i : Fin t => rounds gen i)))
        (fun i => (rounds gen i).x) i) =
      (fun i : Fin (t+1) => (rounds gen i).x) := by
    funext i
    refine Fin.lastCases ?_ (fun j => by rw [Fin.lastCases_castSucc, rounds_castSucc]) i
    rw [Fin.lastCases_last, rounds_last]
    exact (round_x_formula gen t).symm
  rw [hx]
  congr 1
  funext i
  refine Fin.lastCases ?_ (fun j => by rw [Fin.lastCases_castSucc, rounds_castSucc]) i
  rw [Fin.lastCases_last, rounds_last]
  rw [← query_projection gen t, ← round_x_formula gen t]
  exact (answer_raw_projection gen t).symm

private theorem query_mem_target_iff (gen : FeedbackGenerator) (t z : ℕ)
    (hq : (rounds gen t).q = some z) :
    z ∈ diagonalTarget gen ↔
      z ∈ core ∨ ∃ i : Fin (t+1), (rounds gen i).x = z := by
  constructor
  · rintro ⟨s, hs⟩
    change (rounds gen s).x = z at hs
    by_cases hst : s < t+1
    · exact Or.inr ⟨⟨s, hst⟩, hs⟩
    · have hts : t < s := by omega
      by_cases he : Even s
      · left
        rw [← hs, round_x_of_even gen s he]
        exact ⟨s/2, rfl⟩
      · exact False.elim
          (round_x_ne_prior_q_of_not_even gen s he ⟨t, hts⟩ z hq hs)
  · rintro (hc | ⟨i, hi⟩)
    · exact core_subset_target gen hc
    · exact ⟨i, hi⟩

private theorem answer_projection (gen : FeedbackGenerator) (t : ℕ) :
    (rounds gen t).a = match (rounds gen t).q with
      | none => none
      | some z => some (membershipAnswer (diagonalTarget gen) z) := by
  rw [answer_raw_projection]
  split
  · rfl
  · rename_i z hq
    congr 2
    unfold localAnswer membershipAnswer
    classical
    apply decide_eq_decide.mpr
    constructor
    · rintro (hc | rfl | ⟨i, hi⟩)
      · exact core_subset_target gen hc
      · exact ⟨t, rfl⟩
      · exact ⟨i, hi⟩
    · intro hz
      rw [query_mem_target_iff gen t z hq] at hz
      rcases hz with hc | ⟨i, hi⟩
      · exact Or.inl hc
      · by_cases hit : (i : ℕ) = t
        · right; left
          simpa [hit] using hi.symm
        · right; right
          refine ⟨⟨i, by omega⟩, ?_⟩
          exact hi

private theorem follows_protocol (gen : FeedbackGenerator) :
    FollowsProtocol gen (diagonalTarget gen) (diagonalTranscript gen) := by
  intro t
  refine ⟨?_, ?_, ?_⟩
  · exact query_projection gen t
  · exact answer_projection gen t
  · exact output_projection gen t

private theorem clean_diagonal (gen : FeedbackGenerator) :
    Clean (diagonalTranscript gen).presentation (diagonalTarget gen) := by
  intro t
  exact ⟨t, rfl⟩

private theorem complete_diagonal (gen : FeedbackGenerator) :
    Complete (diagonalTranscript gen).presentation (diagonalTarget gen) := by
  intro z hz
  exact hz

noncomputable def diagonalPresenter (gen : FeedbackGenerator) : CausalPresenter where
  next t _ _ _ _ := (diagonalTranscript gen).presentation t

private theorem presented_by_diagonal (gen : FeedbackGenerator) :
    PresentedBy (diagonalPresenter gen) (diagonalTranscript gen) := by
  intro t
  rfl

private theorem scored_subset_core (gen : FeedbackGenerator) :
    scored (diagonalTarget gen) (diagonalTranscript gen).presentation
      (diagonalTranscript gen).output ⊆ core := by
  intro z hz
  rcases hz with ⟨hzK, t, hyt, hzfresh⟩
  by_contra hzcore
  rcases hzK with ⟨s, hs⟩
  change (rounds gen s).x = z at hs
  have hts : t < s := by
    by_contra hnot
    have hle : s ≤ t := by omega
    apply hzfresh
    exact ⟨s, hle, hs⟩
  have hsodd : ¬ Even s := by
    intro hseven
    apply hzcore
    rw [← hs, round_x_of_even gen s hseven]
    exact ⟨s/2, rfl⟩
  apply round_x_ne_prior_y_of_not_even gen s hsodd ⟨t, hts⟩
  change (rounds gen s).x = (rounds gen t).y
  exact hs.trans hyt.symm

end Stage3Work
