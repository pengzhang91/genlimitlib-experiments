import Stage3Model
import GenLimit.Paper17_InfiniteContamination.SharedVanishingPresentation

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


namespace Stage3Work
open Stage3S2B
open Filter
open scoped Topology

private theorem priorValues_card_le (t : ℕ) (r : Fin t → Round) :
    (priorValues r).card ≤ 3 * t := by
  unfold priorValues
  calc
    ((Finset.univ.image fun i => (r i).x) ∪
      (Finset.univ.image fun i => (r i).q.getD 0) ∪
      (Finset.univ.image fun i => (r i).y)).card ≤
        ((Finset.univ.image fun i => (r i).x) ∪
          (Finset.univ.image fun i => (r i).q.getD 0)).card +
        (Finset.univ.image fun i => (r i).y).card := Finset.card_union_le _ _
    _ ≤ ((Finset.univ.image fun i => (r i).x).card +
          (Finset.univ.image fun i => (r i).q.getD 0).card) +
        (Finset.univ.image fun i => (r i).y).card := by
      gcongr
      exact Finset.card_union_le _ _
    _ ≤ t + t + t := by
      have hx : (Finset.univ.image fun i : Fin t => (r i).x).card ≤ t := by
        simpa using (Finset.card_image_le :
          (Finset.univ.image fun i : Fin t => (r i).x).card ≤ Finset.univ.card)
      have hq : (Finset.univ.image fun i : Fin t => (r i).q.getD 0).card ≤ t := by
        simpa using (Finset.card_image_le :
          (Finset.univ.image fun i : Fin t => (r i).q.getD 0).card ≤ Finset.univ.card)
      have hy : (Finset.univ.image fun i : Fin t => (r i).y).card ≤ t := by
        simpa using (Finset.card_image_le :
          (Finset.univ.image fun i : Fin t => (r i).y).card ≤ Finset.univ.card)
      omega
    _ = 3 * t := by omega

private theorem chooseOrdinary_le (prior : Finset ℕ) :
    chooseOrdinary prior ≤ 2 * prior.card + 3 := by
  classical
  let candidates :=
    (Finset.range (prior.card + 1)).image (fun n : ℕ => 2 * n + 3)
  have hinj : Function.Injective (fun n : ℕ => 2 * n + 3) := by
    intro a b h
    have hmul : 2 * a = 2 * b := Nat.add_right_cancel h
    exact Nat.eq_of_mul_eq_mul_left (by omega) hmul
  have hcandidates : candidates.card = prior.card + 1 := by
    dsimp [candidates]
    rw [Finset.card_image_of_injective _ hinj, Finset.card_range]
  obtain ⟨z, hzcan, hznot⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card
      (s := prior) (t := candidates) (by omega)
  rcases Finset.mem_image.mp hzcan with ⟨n, hn, rfl⟩
  have hnle : n ≤ prior.card := by
    simpa only [Finset.mem_range, Nat.lt_add_one_iff] using hn
  calc
    chooseOrdinary prior ≤ 2 * n + 3 := by
      apply Nat.find_min'
      constructor
      · intro hcore
        rcases hcore with ⟨k, hk⟩
        cases k with
        | zero => simp at hk
        | succ k =>
            change 2 ^ (k + 1) = 2 * n + 3 at hk
            rw [pow_succ] at hk
            omega
      · exact hznot
    _ ≤ 2 * prior.card + 3 := by omega

private theorem odd_round_linear_bound (gen : FeedbackGenerator) (t : ℕ)
    (ht : ¬ Even t) : (rounds gen t).x ≤ 6 * t + 3 := by
  rw [round_x_of_not_even gen t ht]
  calc
    chooseOrdinary (priorValues (fun i : Fin t => rounds gen i)) ≤
        2 * (priorValues (fun i : Fin t => rounds gen i)).card + 3 :=
      chooseOrdinary_le _
    _ ≤ 2 * (3 * t) + 3 := by
      gcongr
      exact priorValues_card_le t _
    _ = 6 * t + 3 := by ring


private theorem diagonalTarget_infinite (gen : FeedbackGenerator) :
    (diagonalTarget gen).Infinite := by
  apply (Set.infinite_range_of_injective
    (Nat.pow_right_injective (by omega : 1 < (2 : ℕ)))).mono
  exact core_subset_target gen

private theorem odd_not_even (m : ℕ) : ¬ Even (2 * m + 1) := by
  rw [even_iff_two_dvd]
  omega

private theorem odd_presentation_bound (gen : FeedbackGenerator) (m : ℕ) :
    (diagonalTranscript gen).presentation (2 * m + 1) ≤ 12 * m + 9 := by
  change (rounds gen (2 * m + 1)).x ≤ 12 * m + 9
  have h := odd_round_linear_bound gen (2 * m + 1) (odd_not_even m)
  omega

private noncomputable def targetCount (gen : FeedbackGenerator) (b : ℕ) : ℕ := by
  classical
  exact Nat.count (fun z => z ∈ diagonalTarget gen) b

private theorem target_count_linear_lower (gen : FeedbackGenerator) (n : ℕ) :
    n + 1 ≤ targetCount gen (12 * n + 10) := by
  classical
  let values := (Finset.range (n + 1)).image
    (fun m => (diagonalTranscript gen).presentation (2 * m + 1))
  have hvalues : values.card = n + 1 := by
    dsimp [values]
    rw [Finset.card_image_of_injective, Finset.card_range]
    intro a b hab
    have := presentation_injective gen hab
    omega
  unfold targetCount
  rw [Nat.count_eq_card_filter_range]
  rw [← hvalues]
  apply Finset.card_le_card
  intro z hz
  rcases Finset.mem_image.mp hz with ⟨m, hm, rfl⟩
  have hmn : m ≤ n := by
    simpa only [Finset.mem_range, Nat.lt_add_one_iff] using hm
  apply Finset.mem_filter.mpr
  constructor
  · apply Finset.mem_range.mpr
    have hb := odd_presentation_bound gen m
    omega
  · exact ⟨2 * m + 1, rfl⟩

private theorem target_nth_linear_bound (gen : FeedbackGenerator) (n : ℕ) :
    Nat.nth (fun z => z ∈ diagonalTarget gen) n ≤ 12 * n + 9 := by
  have hcount := target_count_linear_lower gen n
  have hlt : n < targetCount gen (12 * n + 10) := by
    omega
  classical
  unfold targetCount at hlt
  exact Nat.lt_succ_iff.mp (Nat.nth_lt_of_lt_count hlt)

noncomputable def ambientOrder (gen : FeedbackGenerator) : OrderedLanguage where
  carrier := diagonalTarget gen
  enumeration := Nat.nth (fun z => z ∈ diagonalTarget gen)
  enumeration_injective := Nat.nth_injective (diagonalTarget_infinite gen)
  range_enumeration := Nat.range_nth_of_infinite (diagonalTarget_infinite gen)

private theorem ambientOrder_strictMono (gen : FeedbackGenerator) :
    InheritsAmbientOrder (ambientOrder gen) :=
  Nat.nth_strictMono (diagonalTarget_infinite gen)


private theorem core_exponent_lt_bound {z B : ℕ} (hz : z ∈ core) (hzB : z < B) :
    ∃ k < 2 * Nat.sqrt B + 2, 2 ^ k = z := by
  rcases hz with ⟨k, rfl⟩
  refine ⟨k, ?_, rfl⟩
  let q := k / 2
  have hqk : 2 * q ≤ k := by
    dsimp [q]
    omega
  have hkq : k ≤ 2 * q + 1 := by
    dsimp [q]
    omega
  have hpow : 2 ^ (2 * q) ≤ 2 ^ k :=
    Nat.pow_le_pow_right (by omega) hqk
  have hsq : q * q ≤ 2 ^ k := by
    have hbase := Nat.two_mul_sq_add_one_le_two_pow_two_mul q
    have hsq' : q ^ 2 ≤ 2 ^ k := by omega
    simpa [pow_two] using hsq'
  have hsqB : q * q ≤ B := hsq.trans hzB.le
  have hq : q ≤ Nat.sqrt B := Nat.le_sqrt.mpr hsqB
  omega

private noncomputable def coreBelow (B : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range B).filter fun z => z ∈ core

private theorem core_below_card_le (B : ℕ) :
    (coreBelow B).card ≤ 2 * Nat.sqrt B + 2 := by
  classical
  unfold coreBelow
  let exponents := Finset.range (2 * Nat.sqrt B + 2)
  let powers := exponents.image (fun k : ℕ => 2 ^ k)
  calc
    ((Finset.range B).filter fun z => z ∈ core).card ≤ powers.card := by
      apply Finset.card_le_card
      intro z hz
      have hzB := (Finset.mem_filter.mp hz).1
      have hzcore := (Finset.mem_filter.mp hz).2
      rcases core_exponent_lt_bound hzcore (Finset.mem_range.mp hzB) with
        ⟨k, hk, rfl⟩
      exact Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr hk, rfl⟩
    _ ≤ exponents.card := Finset.card_image_le
    _ = 2 * Nat.sqrt B + 2 := Finset.card_range _

private theorem ambient_prefixCount_core_le (gen : FeedbackGenerator) (n : ℕ) :
    (ambientOrder gen).prefixCount core n ≤
      2 * Nat.sqrt (12 * n + 10) + 2 := by
  classical
  let positions := (Finset.range n).filter
    (fun i => (ambientOrder gen).enumeration i ∈ core)
  let values := positions.image (ambientOrder gen).enumeration
  have hcard : values.card = (ambientOrder gen).prefixCount core n := by
    unfold GenLimit.KleinbergWei.OrderedLanguage.prefixCount
    dsimp [values, positions]
    rw [Finset.card_image_of_injective _ (ambientOrder gen).enumeration_injective]
  rw [← hcard]
  calc
    values.card ≤ (coreBelow (12 * n + 10)).card := by
      unfold coreBelow
      apply Finset.card_le_card
      intro z hz
      rcases Finset.mem_image.mp hz with ⟨i, hi, rfl⟩
      have hirange := (Finset.mem_filter.mp hi).1
      have hicore := (Finset.mem_filter.mp hi).2
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_range.mpr ?_, hicore⟩
      have hibound := target_nth_linear_bound gen i
      have hin : i < n := Finset.mem_range.mp hirange
      change Nat.nth (fun z => z ∈ diagonalTarget gen) i < 12 * n + 10
      omega
    _ ≤ 2 * Nat.sqrt (12 * n + 10) + 2 := core_below_card_le _


private theorem sqrt_linear_bound (n : ℕ) :
    Nat.sqrt (12 * n + 10) ≤ 4 * (Nat.sqrt n + 1) := by
  apply Nat.le_of_lt_succ
  rw [Nat.sqrt_lt]
  have hn := Nat.lt_succ_sqrt n
  nlinarith

private theorem ambient_prefixRatio_core_bound (gen : FeedbackGenerator) (n : ℕ) :
    (ambientOrder gen).prefixRatio core n ≤
      10 * (((Nat.sqrt n : ℝ) + 1) / (n : ℝ)) := by
  by_cases hn : n = 0
  · simp [hn]
  · unfold GenLimit.KleinbergWei.OrderedLanguage.prefixRatio
    simp only [hn, if_false]
    rw [← mul_div_assoc]
    apply div_le_div_of_nonneg_right
    · have hcount := ambient_prefixCount_core_le gen n
      have hsqrt := sqrt_linear_bound n
      exact_mod_cast (show (ambientOrder gen).prefixCount core n ≤
        10 * (Nat.sqrt n + 1) by omega)
    · positivity

private theorem ambient_prefixRatio_core_tendsto_zero (gen : FeedbackGenerator) :
    Tendsto ((ambientOrder gen).prefixRatio core) atTop (nhds 0) := by
  apply squeeze_zero
    (fun n => (ambientOrder gen).prefixRatio_nonneg core n)
    (ambient_prefixRatio_core_bound gen)
  simpa only [mul_zero] using
    (GenLimit.InfiniteContamination.tendsto_sparseSqrt_add_one_div.const_mul 10)

private theorem ambient_upperDensity_core_zero (gen : FeedbackGenerator) :
    (ambientOrder gen).upperDensity core = 0 :=
  (ambient_prefixRatio_core_tendsto_zero gen).limsup_eq

private theorem ambient_upperDensity_scored_zero (gen : FeedbackGenerator) :
    (ambientOrder gen).upperDensity
      (scored (diagonalTarget gen) (diagonalTranscript gen).presentation
        (diagonalTranscript gen).output) = 0 := by
  apply le_antisymm
  · calc
      (ambientOrder gen).upperDensity
          (scored (diagonalTarget gen) (diagonalTranscript gen).presentation
            (diagonalTranscript gen).output) ≤
          (ambientOrder gen).upperDensity core :=
        (ambientOrder gen).upperDensity_mono (scored_subset_core gen)
      _ = 0 := ambient_upperDensity_core_zero gen
  · exact (ambientOrder gen).upperDensity_nonneg _


theorem diagonal_negative_claim : NegativeClaim := by
  intro gen _hgen
  refine ⟨diagonalTarget gen, diagonalTarget_mem_class gen,
    diagonalPresenter gen, diagonalTranscript gen, ambientOrder gen, ?_⟩
  exact ⟨rfl, ambientOrder_strictMono gen, presented_by_diagonal gen,
    follows_protocol gen, clean_diagonal gen, presentation_injective gen,
    complete_diagonal gen, ambient_upperDensity_scored_zero gen⟩

end Stage3Work
