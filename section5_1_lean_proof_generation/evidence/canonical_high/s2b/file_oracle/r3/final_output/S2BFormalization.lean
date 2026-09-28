import Stage3Model
import GenLimit.Paper10_UnionClosednessOfLanguageGeneration.Cardinality
import GenLimit.Paper39_DenseGeneration.Abstract.Density
import Mathlib.Data.Nat.Nth

open Set Filter

namespace Stage3S2BProof

open Stage3S2B

structure Round where
  presentation : ℕ
  query : Option ℕ
  answer : Option Bool
  output : ℕ

def special (k : ℕ) : ℕ := 4 * k + 3

theorem special_injective : Function.Injective special := by
  intro a b h
  simp [special] at h
  omega

theorem special_not_core (k : ℕ) : special k ∉ core := by
  rintro ⟨j, hj⟩
  have hmod : special k % 4 = 3 := by simp [special]
  rw [← hj] at hmod
  rcases j with _ | j
  · simp at hmod
  rcases j with _ | j
  · simp at hmod
  · have hd : 4 ∣ 2 ^ (j + 1 + 1) := by
      refine ⟨2 ^ j, ?_⟩
      rw [show j + 1 + 1 = j + 2 by omega, pow_add]
      norm_num
      ring
    have hz : 2 ^ (j + 1 + 1) % 4 = 0 := Nat.mod_eq_zero_of_dvd hd
    rw [hz] at hmod
    contradiction

def blocked (h : Fin t → Round) : Set ℕ :=
  Set.range (fun i => (h i).presentation) ∪
  Set.range (fun i => (h i).output) ∪
  {z | ∃ i, (h i).query = some z ∧ (h i).answer = some false}

theorem blocked_finite (h : Fin t → Round) : (blocked h).Finite := by
  unfold blocked
  apply ((Set.finite_range fun i => (h i).presentation).union
    (Set.finite_range fun i => (h i).output)).union
  apply (Set.finite_range fun i => (h i).query.getD 0).subset
  rintro z ⟨i, hiq, -⟩
  refine ⟨i, ?_⟩
  simp [hiq]

theorem exists_unblocked_special (h : Fin t → Round) :
    ∃ k, special k ∉ blocked h := by
  have hinf : (Set.range special).Infinite :=
    Set.infinite_range_of_injective special_injective
  obtain ⟨z, ⟨k, rfl⟩, hz⟩ := (hinf.diff (blocked_finite h)).nonempty
  exact ⟨k, hz⟩

noncomputable def chosenIndex (h : Fin t → Round) : ℕ := by
  classical
  exact Nat.find (exists_unblocked_special h)

noncomputable def choosePresentation (t : ℕ) (h : Fin t → Round) : ℕ :=
  if ht : Even t then 2 ^ (t / 2) else special (chosenIndex h)

noncomputable def nextRound (gen : FeedbackGenerator) (t : ℕ)
    (h : Fin t → Round) : Round := by
  classical
  let x := choosePresentation t h
  let xs : Fin (t + 1) → ℕ := Fin.lastCases x (fun i => (h i).presentation)
  let oldAnswers : Fin t → Option Bool := fun i => (h i).answer
  let q := gen.query t xs oldAnswers
  let a := match q with
    | none => none
    | some z => some (decide (z ∈ core ∨ ∃ i, (h i).presentation = z ∨ x = z))
  let answers : Fin (t + 1) → Option Bool := Fin.lastCases a oldAnswers
  exact ⟨x, q, a, gen.output t xs answers⟩

noncomputable def history (gen : FeedbackGenerator) :
    (t : ℕ) → Fin t → Round
  | 0 => Fin.elim0
  | t + 1 => Fin.lastCases (nextRound gen t (history gen t)) (history gen t)

noncomputable def tr (gen : FeedbackGenerator) : Transcript where
  presentation t := (nextRound gen t (history gen t)).presentation
  query t := (nextRound gen t (history gen t)).query
  answer t := (nextRound gen t (history gen t)).answer
  output t := (nextRound gen t (history gen t)).output

def admitted (gen : FeedbackGenerator) : Set ℕ :=
  Set.range (fun r => (tr gen).presentation (2 * r + 1))

def target (gen : FeedbackGenerator) : Language := core ∪ admitted gen

noncomputable def presenter (gen : FeedbackGenerator) : CausalPresenter where
  next t xs qs ans ys :=
    if h : ∀ i : Fin t,
        xs i = (history gen t i).presentation ∧
        qs i = (history gen t i).query ∧
        ans i = (history gen t i).answer ∧
        ys i = (history gen t i).output
    then choosePresentation t (history gen t)
    else Nat.nth (fun z => z ∈ target gen ∧ z ∉ Set.range xs) 0


theorem history_apply (gen : FeedbackGenerator) (i : Fin t) :
    history gen t i = nextRound gen i (history gen i) := by
  induction t with
  | zero => exact Fin.elim0 i
  | succ t ih =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [history]
      · simpa [history] using ih j

theorem tr_eq_history (gen : FeedbackGenerator) (i : Fin t) :
    ((tr gen).presentation i, (tr gen).query i,
      (tr gen).answer i, (tr gen).output i) =
    ((history gen t i).presentation, (history gen t i).query,
      (history gen t i).answer, (history gen t i).output) := by
  rw [history_apply]
  rfl

theorem presentation_eq_choose (gen : FeedbackGenerator) (t : ℕ) :
    (tr gen).presentation t = choosePresentation t (history gen t) := by
  rfl

theorem even_presentation (gen : FeedbackGenerator) (r : ℕ) :
    (tr gen).presentation (2 * r) = 2 ^ r := by
  rw [presentation_eq_choose]
  simp [choosePresentation, show Even (2 * r) by exact ⟨r, by omega⟩]

theorem odd_presentation (gen : FeedbackGenerator) (r : ℕ) :
    (tr gen).presentation (2 * r + 1) =
      special (chosenIndex (history gen (2 * r + 1))) := by
  rw [presentation_eq_choose]
  have hodd : ¬ Even (2 * r + 1) := by
    rintro ⟨k, hk⟩
    omega
  simp [choosePresentation, hodd]

theorem chosen_not_blocked (h : Fin t → Round) :
    special (chosenIndex h) ∉ blocked h := by
  classical
  exact Nat.find_spec (exists_unblocked_special h)



theorem range_ncard_le_fin (f : Fin t → ℕ) : (Set.range f).ncard ≤ t := by
  rw [← Set.image_univ]
  calc
    (f '' Set.univ).ncard ≤ Set.univ.ncard := Set.ncard_image_le
    _ = t := by simp

theorem blocked_ncard_le (h : Fin t → Round) : (blocked h).ncard ≤ 3 * t := by
  let neg : Set ℕ := {z | ∃ i, (h i).query = some z ∧ (h i).answer = some false}
  have hnegsub : neg ⊆ Set.range (fun i => (h i).query.getD 0) := by
    rintro z ⟨i, hiq, -⟩
    exact ⟨i, by simp [hiq]⟩
  have hneg : neg.ncard ≤ t := by
    calc
      neg.ncard ≤ (Set.range (fun i => (h i).query.getD 0)).ncard :=
        Set.ncard_le_ncard hnegsub (Set.finite_range _)
      _ ≤ t := range_ncard_le_fin _
  unfold blocked
  calc
    ((Set.range fun i => (h i).presentation) ∪
      (Set.range fun i => (h i).output) ∪ neg).ncard
        ≤ (Set.range fun i => (h i).presentation).ncard +
          (Set.range fun i => (h i).output).ncard + neg.ncard := by
            exact (Set.ncard_union_le _ _).trans
              (Nat.add_le_add_right (Set.ncard_union_le _ _) _)
    _ ≤ t + t + t := by
      exact Nat.add_le_add (Nat.add_le_add (range_ncard_le_fin _) (range_ncard_le_fin _)) hneg
    _ = 3 * t := by omega

theorem chosenIndex_le (h : Fin t → Round) : chosenIndex h ≤ 3 * t := by
  classical
  let F := (blocked_finite h).toFinset
  have hsubset : (Finset.range (chosenIndex h)).image special ⊆ F := by
    intro z hz
    simp only [Finset.mem_image, Finset.mem_range] at hz
    obtain ⟨k, hk, rfl⟩ := hz
    have hmem : special k ∈ blocked h := by
      by_contra hnot
      exact Nat.find_min (exists_unblocked_special h) hk hnot
    simpa [F] using hmem
  have hcard : ((Finset.range (chosenIndex h)).image special).card = chosenIndex h := by
    rw [Finset.card_image_iff.mpr]
    · simp
    · exact fun _ _ _ _ heq => special_injective heq
  calc
    chosenIndex h = ((Finset.range (chosenIndex h)).image special).card := hcard.symm
    _ ≤ F.card := Finset.card_le_card hsubset
    _ = (blocked h).ncard := by
      rw [Set.ncard_eq_toFinset_card (blocked h) (blocked_finite h)]
    _ ≤ 3 * t := blocked_ncard_le h

theorem odd_presentation_le (gen : FeedbackGenerator) (r : ℕ) :
    (tr gen).presentation (2 * r + 1) ≤ 24 * r + 15 := by
  rw [odd_presentation]
  unfold special
  have h := chosenIndex_le (history gen (2 * r + 1))
  omega



theorem tr_presentation_history (gen : FeedbackGenerator) (i : Fin t) :
    (tr gen).presentation i = (history gen t i).presentation := by
  rw [history_apply]
  rfl

theorem tr_query_history (gen : FeedbackGenerator) (i : Fin t) :
    (tr gen).query i = (history gen t i).query := by
  rw [history_apply]
  rfl

theorem tr_answer_history (gen : FeedbackGenerator) (i : Fin t) :
    (tr gen).answer i = (history gen t i).answer := by
  rw [history_apply]
  rfl

theorem tr_output_history (gen : FeedbackGenerator) (i : Fin t) :
    (tr gen).output i = (history gen t i).output := by
  rw [history_apply]
  rfl

theorem odd_not_previous_presentation (gen : FeedbackGenerator) (r s : ℕ)
    (hs : s < 2 * r + 1) :
    (tr gen).presentation (2 * r + 1) ≠ (tr gen).presentation s := by
  rw [odd_presentation]
  intro heq
  apply chosen_not_blocked (history gen (2 * r + 1))
  left
  left
  refine ⟨⟨s, hs⟩, ?_⟩
  change (history gen (2 * r + 1) ⟨s, hs⟩).presentation = _
  rw [← tr_presentation_history]
  exact heq.symm

theorem odd_not_previous_output (gen : FeedbackGenerator) (r s : ℕ)
    (hs : s < 2 * r + 1) :
    (tr gen).presentation (2 * r + 1) ≠ (tr gen).output s := by
  rw [odd_presentation]
  intro heq
  apply chosen_not_blocked (history gen (2 * r + 1))
  left
  right
  refine ⟨⟨s, hs⟩, ?_⟩
  change (history gen (2 * r + 1) ⟨s, hs⟩).output = _
  rw [← tr_output_history]
  exact heq.symm

theorem admitted_subset_ordinary (gen : FeedbackGenerator) :
    admitted gen ⊆ ordinary := by
  rintro z ⟨r, rfl⟩
  change (tr gen).presentation (2 * r + 1) ∈ ordinary
  rw [odd_presentation]
  exact special_not_core _

theorem target_mem_class (gen : FeedbackGenerator) : target gen ∈ targetClass := by
  exact ⟨admitted gen, admitted_subset_ordinary gen, rfl⟩

theorem presentation_clean (gen : FeedbackGenerator) :
    Clean (tr gen).presentation (target gen) := by
  intro t
  rcases Nat.even_or_odd t with ⟨r, hr⟩ | ⟨r, hr⟩
  · have ht : t = 2 * r := by omega
    subst t
    left
    have hp : (tr gen).presentation (r + r) = 2 ^ r := by
      simpa [two_mul] using even_presentation gen r
    rw [hp]
    exact ⟨r, rfl⟩
  · have ht : t = 2 * r + 1 := by omega
    subst t
    right
    exact ⟨r, rfl⟩

theorem presentation_ne_of_lt (gen : FeedbackGenerator) {s t : ℕ} (hst : s < t) :
    (tr gen).presentation s ≠ (tr gen).presentation t := by
  rcases Nat.even_or_odd t with ⟨r, hr⟩ | ⟨r, hr⟩
  · have ht : t = 2 * r := by omega
    subst t
    rcases Nat.even_or_odd s with ⟨q, hq⟩ | ⟨q, hq⟩
    · have hs : s = 2 * q := by omega
      subst s
      have hpq : (tr gen).presentation (q + q) = 2 ^ q := by
        simpa [two_mul] using even_presentation gen q
      have hpr : (tr gen).presentation (r + r) = 2 ^ r := by
        simpa [two_mul] using even_presentation gen r
      rw [hpq, hpr]
      intro heq
      have : q = r := Nat.pow_right_injective (by norm_num) heq
      omega
    · have hs : s = 2 * q + 1 := by omega
      subst s
      rw [odd_presentation]
      have hpr : (tr gen).presentation (r + r) = 2 ^ r := by
        simpa [two_mul] using even_presentation gen r
      rw [hpr]
      intro heq
      exact special_not_core _ ⟨r, heq.symm⟩
  · have ht : t = 2 * r + 1 := by omega
    subst t
    exact fun heq => odd_not_previous_presentation gen r s hst heq.symm

theorem presentation_injective (gen : FeedbackGenerator) :
    Function.Injective (tr gen).presentation := by
  intro s t hst
  rcases lt_trichotomy s t with hlt | heq | hgt
  · exact (presentation_ne_of_lt gen hlt hst).elim
  · exact heq
  · exact (presentation_ne_of_lt gen hgt hst.symm).elim

theorem presentation_complete (gen : FeedbackGenerator) :
    Complete (tr gen).presentation (target gen) := by
  intro z hz
  rcases hz with hz | hz
  · obtain ⟨r, rfl⟩ := hz
    exact ⟨2 * r, even_presentation gen r⟩
  · obtain ⟨r, rfl⟩ := hz
    exact ⟨2 * r + 1, rfl⟩

theorem scored_subset_core (gen : FeedbackGenerator) :
    scored (target gen) (tr gen).presentation (tr gen).output ⊆ core := by
  intro z hz
  rcases hz with ⟨hzK, t, hyt, hzobs⟩
  rcases hzK with hzcore | ⟨r, hzr⟩
  · exact hzcore
  · by_contra hzcore
    have hfuture : t < 2 * r + 1 := by
      by_contra hnot
      apply hzobs
      exact ⟨2 * r + 1, Nat.le_of_not_gt hnot, hzr⟩
    apply odd_not_previous_output gen r t hfuture
    calc
      (tr gen).presentation (2 * r + 1) = z := hzr
      _ = (tr gen).output t := hyt.symm



theorem prefix_presentations (gen : FeedbackGenerator) (t : ℕ) :
    (fun i : Fin (t + 1) => (tr gen).presentation i) =
      Fin.lastCases ((tr gen).presentation t)
        (fun i : Fin t => (history gen t i).presentation) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp
  · simp only [Fin.lastCases_castSucc]
    exact tr_presentation_history gen j

theorem prefix_answers (gen : FeedbackGenerator) (t : ℕ) :
    (fun i : Fin (t + 1) => (tr gen).answer i) =
      Fin.lastCases ((tr gen).answer t)
        (fun i : Fin t => (history gen t i).answer) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp
  · simp only [Fin.lastCases_castSucc]
    exact tr_answer_history gen j

theorem prior_answers (gen : FeedbackGenerator) (t : ℕ) :
    (fun i : Fin t => (tr gen).answer i) =
      (fun i : Fin t => (history gen t i).answer) := by
  funext i
  exact tr_answer_history gen i

theorem query_protocol (gen : FeedbackGenerator) (t : ℕ) :
    (tr gen).query t = gen.query t
      (fun i => (tr gen).presentation i) (fun i => (tr gen).answer i) := by
  rw [prefix_presentations, prior_answers]
  rfl

theorem output_protocol (gen : FeedbackGenerator) (t : ℕ) :
    (tr gen).output t = gen.output t
      (fun i => (tr gen).presentation i) (fun i => (tr gen).answer i) := by
  rw [prefix_presentations, prefix_answers]
  rfl

theorem presented_by (gen : FeedbackGenerator) : PresentedBy (presenter gen) (tr gen) := by
  intro t
  unfold presenter
  simp only
  rw [dif_pos]
  · rfl
  · intro i
    exact ⟨tr_presentation_history gen i, tr_query_history gen i,
      tr_answer_history gen i, tr_output_history gen i⟩

theorem odd_not_previous_negative (gen : FeedbackGenerator) (r t z : ℕ)
    (ht : t < 2 * r + 1) (hq : (tr gen).query t = some z)
    (ha : (tr gen).answer t = some false) :
    (tr gen).presentation (2 * r + 1) ≠ z := by
  rw [odd_presentation]
  intro heq
  apply chosen_not_blocked (history gen (2 * r + 1))
  right
  refine ⟨⟨t, ht⟩, ?_, ?_⟩
  · rw [← tr_query_history, heq]
    exact hq
  · rw [← tr_answer_history]
    exact ha



def positiveAt (gen : FeedbackGenerator) (t z : ℕ) : Prop :=
  z ∈ core ∨ ∃ i : Fin t,
    (history gen t i).presentation = z ∨ choosePresentation t (history gen t) = z

theorem answer_none_of_query_none (gen : FeedbackGenerator) (t : ℕ)
    (hq : (tr gen).query t = none) : (tr gen).answer t = none := by
  classical
  unfold tr at hq ⊢
  dsimp [nextRound] at hq ⊢
  rw [hq]

theorem answer_true_of_query_some (gen : FeedbackGenerator) (t z : ℕ)
    (hq : (tr gen).query t = some z) (hp : positiveAt gen t z) :
    (tr gen).answer t = some true := by
  classical
  unfold tr at hq ⊢
  dsimp [nextRound] at hq ⊢
  rw [hq]
  simp [positiveAt] at hp ⊢
  exact hp

theorem answer_false_of_query_some (gen : FeedbackGenerator) (t z : ℕ)
    (hq : (tr gen).query t = some z) (hp : ¬ positiveAt gen t z) :
    (tr gen).answer t = some false := by
  classical
  unfold tr at hq ⊢
  dsimp [nextRound] at hq ⊢
  rw [hq]
  simp [positiveAt] at hp ⊢
  exact hp

theorem positiveAt_mem_target (gen : FeedbackGenerator) {t z : ℕ}
    (hp : positiveAt gen t z) : z ∈ target gen := by
  rcases hp with hz | ⟨i, hi | hi⟩
  · exact Or.inl hz
  · have hm := presentation_clean gen i
    rw [tr_presentation_history] at hm
    exact hi ▸ hm
  · have hm := presentation_clean gen t
    rw [presentation_eq_choose] at hm
    exact hi ▸ hm

theorem not_positiveAt_not_mem_target_of_query (gen : FeedbackGenerator) {t z : ℕ}
    (hq : (tr gen).query t = some z) (hp : ¬ positiveAt gen t z) :
    z ∉ target gen := by
  classical
  intro hz
  rcases hz with hzcore | ⟨r, hr⟩
  · exact hp (Or.inl hzcore)
  · by_cases hlt : 2 * r + 1 < t
    · apply hp
      right
      refine ⟨⟨2 * r + 1, hlt⟩, Or.inl ?_⟩
      rw [← tr_presentation_history]
      exact hr
    · by_cases heq : 2 * r + 1 = t
      · apply hp
        right
        refine ⟨⟨0, by omega⟩, Or.inr ?_⟩
        rw [← presentation_eq_choose, ← heq]
        exact hr
      · have hfuture : t < 2 * r + 1 := by omega
        have ha : (tr gen).answer t = some false :=
          answer_false_of_query_some gen t z hq hp
        exact (odd_not_previous_negative gen r t z hfuture hq ha) hr

theorem follows_protocol (gen : FeedbackGenerator) :
    FollowsProtocol gen (target gen) (tr gen) := by
  classical
  intro t
  refine ⟨query_protocol gen t, ?_, output_protocol gen t⟩
  cases hq : (tr gen).query t with
  | none =>
      rw [answer_none_of_query_none gen t hq]
  | some z =>
      by_cases hz : z ∈ target gen
      · have hp : positiveAt gen t z := by
          by_contra hnp
          exact not_positiveAt_not_mem_target_of_query gen hq hnp hz
        rw [answer_true_of_query_some gen t z hq hp]
        unfold membershipAnswer
        simp [hz]
      · have hp : ¬ positiveAt gen t z := fun hp => hz (positiveAt_mem_target gen hp)
        rw [answer_false_of_query_some gen t z hq hp]
        unfold membershipAnswer
        simp [hz]

def encodeSubset (A : Set ordinary) : Language :=
  core ∪ ((fun z : ordinary => (z : ℕ)) '' A)

theorem encodeSubset_mem (A : Set ordinary) : encodeSubset A ∈ targetClass := by
  refine ⟨(fun z : ordinary => (z : ℕ)) '' A, ?_, rfl⟩
  rintro z ⟨w, -, rfl⟩
  exact w.property

theorem encodeSubset_injective : Function.Injective encodeSubset := by
  intro A B h
  ext z
  have hz : (z : ℕ) ∉ core := z.property
  have heq : (z : ℕ) ∈ encodeSubset A ↔ (z : ℕ) ∈ encodeSubset B := by rw [h]
  simpa [encodeSubset, hz] using heq

theorem targetClass_not_countable : ¬ targetClass.Countable := by
  intro hc
  let f : Set ordinary → targetClass := fun A => ⟨encodeSubset A, encodeSubset_mem A⟩
  have hf : Function.Injective f := by
    intro A B h
    apply encodeSubset_injective
    exact congrArg Subtype.val h
  letI : Countable targetClass := hc
  letI : Countable (Set ordinary) := hf.countable
  have hord : ordinary.Infinite := by
    apply (Set.infinite_range_of_injective special_injective).mono
    rintro z ⟨k, rfl⟩
    exact special_not_core k
  letI : Infinite ordinary := Set.infinite_coe_iff.mpr hord
  exact GenLimit.UnionClosedness.powerSet_not_countable ordinary inferInstance

theorem uniform_positive : UniformlyGeneratableWithoutSamples := by
  refine ⟨fun t => 2 ^ t, ?_, 0, ?_⟩
  · exact Nat.pow_right_injective (by norm_num)
  · intro K hK t ht
    obtain ⟨A, hA, rfl⟩ := hK
    exact Or.inl ⟨t, rfl⟩


theorem core_infinite : core.Infinite := by
  exact Set.infinite_range_of_injective (Nat.pow_right_injective (by norm_num))

theorem target_infinite (gen : FeedbackGenerator) : (target gen).Infinite := by
  exact core_infinite.mono (fun _ hz => Or.inl hz)

noncomputable def orderedTarget (gen : FeedbackGenerator) : OrderedLanguage := by
  classical
  exact {
  carrier := target gen
  enumeration := Nat.nth (fun z => z ∈ target gen)
  enumeration_injective := Nat.nth_injective (target_infinite gen)
  range_enumeration := Nat.range_nth_of_infinite (target_infinite gen)
  }

theorem orderedTarget_ambient (gen : FeedbackGenerator) :
    InheritsAmbientOrder (orderedTarget gen) := by
  exact Nat.nth_strictMono (target_infinite gen)

noncomputable def targetCount (gen : FeedbackGenerator) (m : ℕ) : ℕ := by
  classical
  exact Nat.count (fun z => z ∈ target gen) m

theorem target_count_lower (gen : FeedbackGenerator) (n : ℕ) :
    n + 1 ≤ targetCount gen (24 * n + 16) := by
  classical
  unfold targetCount
  rw [Nat.count_eq_card_filter_range]
  let S := (Finset.range (n + 1)).image (fun r => (tr gen).presentation (2 * r + 1))
  have hcard : S.card = n + 1 := by
    rw [Finset.card_image_iff.mpr]
    · simp [S]
    · intro a ha b hb hab
      have hidx := presentation_injective gen hab
      omega
  rw [← hcard]
  apply Finset.card_le_card
  intro z hz
  simp only [S, Finset.mem_image, Finset.mem_range] at hz
  obtain ⟨r, hr, rfl⟩ := hz
  simp only [Finset.mem_filter, Finset.mem_range]
  refine ⟨?_, ?_⟩
  · have hle := odd_presentation_le gen r
    omega
  · exact presentation_clean gen (2 * r + 1)

theorem orderedTarget_le (gen : FeedbackGenerator) (n : ℕ) :
    (orderedTarget gen).enumeration n ≤ 24 * n + 15 := by
  classical
  change Nat.nth (fun z => z ∈ target gen) n ≤ _
  have hc : n < targetCount gen (24 * n + 16) := by
    have := target_count_lower gen n
    omega
  unfold targetCount at hc
  have hlt := Nat.nth_lt_of_lt_count (p := fun z => z ∈ target gen) hc
  omega

noncomputable def coreExponent (z : ℕ) : ℕ := by
  classical
  exact if hz : z ∈ core then Nat.find hz else 0

theorem pow_coreExponent {z : ℕ} (hz : z ∈ core) : 2 ^ coreExponent z = z := by
  classical
  simp only [coreExponent, dif_pos hz]
  exact Nat.find_spec hz

theorem log2_linear_le (n : ℕ) :
    Nat.log2 (24 * n + 16) ≤ 5 + Nat.log2 (n + 1) := by
  rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
  calc
    Nat.log 2 (24 * n + 16) ≤ Nat.log 2 ((n + 1) * 32) := by
      apply Nat.log_monotone
      omega
    _ = Nat.log 2 (n + 1) + 5 := by
      rw [show (n + 1) * 32 = (((((n + 1) * 2) * 2) * 2) * 2) * 2 by ring]
      rw [Nat.log_mul_base (by norm_num : 1 < 2) (by positivity)]
      rw [Nat.log_mul_base (by norm_num : 1 < 2) (by positivity)]
      rw [Nat.log_mul_base (by norm_num : 1 < 2) (by positivity)]
      rw [Nat.log_mul_base (by norm_num : 1 < 2) (by positivity)]
      rw [Nat.log_mul_base (by norm_num : 1 < 2) (by positivity)]
    _ = 5 + Nat.log 2 (n + 1) := by omega

theorem prefixCount_core_le (gen : FeedbackGenerator) (n : ℕ) :
    (orderedTarget gen).prefixCount core n ≤ Nat.log2 (24 * n + 16) + 1 := by
  classical
  unfold GenLimit.KleinbergWei.OrderedLanguage.prefixCount
  let S := (Finset.range n).filter fun i => (orderedTarget gen).enumeration i ∈ core
  let T := Finset.range (Nat.log2 (24 * n + 16) + 1)
  change S.card ≤ Nat.log2 (24 * n + 16) + 1
  calc
    S.card ≤ T.card := by
      apply Finset.card_le_card_of_injOn (fun i => coreExponent ((orderedTarget gen).enumeration i))
      · intro i hi
        change i ∈ S at hi
        simp only [S, Finset.mem_filter, Finset.mem_range] at hi
        change coreExponent ((orderedTarget gen).enumeration i) ∈ T
        simp only [T, Finset.mem_range]
        have hp := pow_coreExponent hi.2
        have henum := orderedTarget_le gen i
        have hin : i < n := hi.1
        apply Nat.lt_succ_of_le
        rw [Nat.le_log2 (by omega : 24 * n + 16 ≠ 0)]
        rw [hp]
        omega
      · intro a ha b hb heq
        change a ∈ S at ha
        change b ∈ S at hb
        simp only [S, Finset.mem_filter, Finset.mem_range] at ha hb
        apply (orderedTarget gen).enumeration_injective
        rw [← pow_coreExponent ha.2, ← pow_coreExponent hb.2]
        change coreExponent ((orderedTarget gen).enumeration a) =
          coreExponent ((orderedTarget gen).enumeration b) at heq
        rw [heq]
    _ = Nat.log2 (24 * n + 16) + 1 := by simp [T]


theorem log2_succ_le (n : ℕ) (hn : n ≠ 0) :
    Nat.log2 (n + 1) ≤ Nat.log2 n + 1 := by
  rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
  calc
    Nat.log 2 (n + 1) ≤ Nat.log 2 (n * 2) := by
      apply Nat.log_monotone
      omega
    _ = Nat.log 2 n + 1 := Nat.log_mul_base (by norm_num) hn

theorem prefixCount_core_le_log (gen : FeedbackGenerator) (n : ℕ) :
    (orderedTarget gen).prefixCount core n ≤ 7 + Nat.log2 n := by
  by_cases hn : n = 0
  · subst n
    have hzero := (orderedTarget gen).prefixCount_le core 0
    omega
  · have hcount := prefixCount_core_le gen n
    have hlinear := log2_linear_le n
    have hsucc := log2_succ_le n hn
    omega

theorem prefixRatio_core_tendsto (gen : FeedbackGenerator) :
    Tendsto ((orderedTarget gen).prefixRatio core) atTop (nhds 0) := by
  apply squeeze_zero
    (fun n => (orderedTarget gen).prefixRatio_nonneg core n)
    (fun n => ?_)
    (GenLimit.tendsto_countingError_div 7)
  by_cases hn : n = 0
  · simp [hn]
  · simp only [GenLimit.KleinbergWei.OrderedLanguage.prefixRatio, hn, if_false]
    apply div_le_div_of_nonneg_right
    · exact_mod_cast prefixCount_core_le_log gen n
    · positivity

theorem upperDensity_core (gen : FeedbackGenerator) :
    (orderedTarget gen).upperDensity core = 0 := by
  exact (prefixRatio_core_tendsto gen).limsup_eq

theorem upperDensity_scored (gen : FeedbackGenerator) :
    (orderedTarget gen).upperDensity
      (scored (target gen) (tr gen).presentation (tr gen).output) = 0 := by
  apply le_antisymm
  · calc
      (orderedTarget gen).upperDensity
          (scored (target gen) (tr gen).presentation (tr gen).output)
        ≤ (orderedTarget gen).upperDensity core :=
          (orderedTarget gen).upperDensity_mono (scored_subset_core gen)
      _ = 0 := upperDensity_core gen
  · exact (orderedTarget gen).upperDensity_nonneg _

theorem negative_claim : NegativeClaim := by
  intro gen hvalid
  refine ⟨target gen, target_mem_class gen, presenter gen, tr gen, orderedTarget gen, ?_⟩
  exact ⟨rfl, orderedTarget_ambient gen, presented_by gen, follows_protocol gen,
    presentation_clean gen, presentation_injective gen, presentation_complete gen,
    upperDensity_scored gen⟩

end Stage3S2BProof

theorem stage3_result : Stage3S2B.MainClaim := by
  exact ⟨Stage3S2BProof.targetClass_not_countable,
    Stage3S2BProof.uniform_positive, Stage3S2BProof.negative_claim⟩
