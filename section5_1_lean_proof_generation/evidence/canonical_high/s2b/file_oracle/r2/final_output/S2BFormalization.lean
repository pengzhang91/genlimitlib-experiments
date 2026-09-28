import Stage3Model
import GenLimit.Paper10_UnionClosednessOfLanguageGeneration.Cardinality
import GenLimit.Paper39_DenseGeneration.Abstract.Density
import Mathlib.Order.OrderIsoNat

open Set Function Filter
open scoped Topology

namespace Stage3Proof

open Stage3S2B

structure Round where
  presentation : ℕ
  query : Option ℕ
  answer : Option Bool
  output : ℕ

def oddCode (n : ℕ) : ℕ := 2 * n + 3

theorem oddCode_injective : Function.Injective oddCode := by
  intro a b h
  simp [oddCode] at h
  omega

theorem oddCode_not_core (n : ℕ) : oddCode n ∉ core := by
  rintro ⟨k, hk⟩
  cases k with
  | zero => simp [oddCode] at hk
  | succ k =>
      have heven : Even (2 ^ (k + 1)) := by
        refine ⟨2 ^ k, ?_⟩
        rw [pow_succ]
        omega
      have hodd : Odd (oddCode n) := ⟨n + 1, by simp [oddCode]; omega⟩
      change 2 ^ (k + 1) = oddCode n at hk
      rw [hk] at heven
      exact (Nat.not_even_iff_odd.mpr hodd) heven

def queryValue : Option ℕ → ℕ
  | none => 0
  | some z => z

def Safe {t : ℕ} (h : Fin t → Round) (n : ℕ) : Prop :=
  ∀ i, oddCode n ≠ (h i).presentation ∧
    oddCode n ≠ (h i).output ∧ (h i).query ≠ some (oddCode n)

theorem exists_safe {t : ℕ} (h : Fin t → Round) : ∃ n, Safe h n := by
  let B := ∑ i : Fin t,
    ((h i).presentation + (h i).output + queryValue (h i).query + 1)
  refine ⟨B, ?_⟩
  intro i
  have hs := Finset.single_le_sum
    (s := Finset.univ) (f := fun j : Fin t =>
      (h j).presentation + (h j).output + queryValue (h j).query + 1)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have hB : (h i).presentation + (h i).output + queryValue (h i).query + 1 ≤ B := by
    simpa [B] using hs
  have hbig : B < oddCode B := by
    simp [oddCode]
    omega
  have hp : (h i).presentation < oddCode B :=
    lt_of_le_of_lt (by omega) hbig
  have hy : (h i).output < oddCode B :=
    lt_of_le_of_lt (by omega) hbig
  refine ⟨ne_of_gt hp, ne_of_gt hy, ?_⟩
  cases hq : (h i).query with
  | none => simp [hq]
  | some q =>
      intro heq
      have hB' : (h i).presentation + (h i).output + q + 1 ≤ B := by
        simpa [hq, queryValue] using hB
      have hqB : q < oddCode B := by
        exact lt_of_le_of_lt (by omega) hbig
      have : oddCode B = q := by simpa [hq] using heq.symm
      omega

def forbidden {t : ℕ} (h : Fin t → Round) : Finset ℕ :=
  (Finset.univ.image fun i => (h i).presentation) ∪
  (Finset.univ.image fun i => (h i).output) ∪
  (Finset.univ.image fun i => queryValue (h i).query)

theorem forbidden_card_le {t : ℕ} (h : Fin t → Round) :
    (forbidden h).card ≤ 3 * t := by
  unfold forbidden
  let A := Finset.univ.image fun i => (h i).presentation
  let B := Finset.univ.image fun i => (h i).output
  let C := Finset.univ.image fun i => queryValue (h i).query
  change (A ∪ B ∪ C).card ≤ 3 * t
  calc
    (A ∪ B ∪ C).card ≤ (A ∪ B).card + C.card := Finset.card_union_le _ _
    _ ≤ (A.card + B.card) + C.card := Nat.add_le_add_right (Finset.card_union_le _ _) _
    _ ≤ t + t + t := by
      have hA : A.card ≤ t := by simpa [A] using (Finset.card_image_le (s := Finset.univ) (f := fun i : Fin t => (h i).presentation))
      have hB : B.card ≤ t := by simpa [B] using (Finset.card_image_le (s := Finset.univ) (f := fun i : Fin t => (h i).output))
      have hC : C.card ≤ t := by simpa [C] using (Finset.card_image_le (s := Finset.univ) (f := fun i : Fin t => queryValue (h i).query))
      omega
    _ = 3 * t := by omega

theorem exists_safe_le {t : ℕ} (h : Fin t → Round) :
    ∃ n ≤ 3 * t, Safe h n := by
  classical
  let candidates := (Finset.range (3 * t + 1)).image oddCode
  have hcand : candidates.card = 3 * t + 1 := by
    simp [candidates, Finset.card_image_of_injective _ oddCode_injective]
  have hcard : (forbidden h).card < candidates.card := by
    rw [hcand]
    exact lt_of_le_of_lt (forbidden_card_le h) (by omega)
  obtain ⟨z, hzc, hzf⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcard
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hzc
  have hnlt : n < 3 * t + 1 := by simpa using hn
  refine ⟨n, by omega, ?_⟩
  intro i
  refine ⟨?_, ?_, ?_⟩
  · intro heq
    apply hzf
    unfold forbidden
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
    exact Or.inl (Or.inl ⟨i, heq.symm⟩)
  · intro heq
    apply hzf
    unfold forbidden
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
    exact Or.inl (Or.inr ⟨i, heq.symm⟩)
  · intro heq
    apply hzf
    unfold forbidden
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
    right
    refine ⟨i, ?_⟩
    simp [heq, queryValue]

noncomputable def freshIndex {t : ℕ} (h : Fin t → Round) : ℕ := by
  classical
  exact Nat.find (exists_safe h)

theorem freshIndex_safe {t : ℕ} (h : Fin t → Round) :
    Safe h (freshIndex h) := by
  classical
  exact Nat.find_spec (exists_safe h)

theorem freshIndex_le {t : ℕ} (h : Fin t → Round) :
    freshIndex h ≤ 3 * t := by
  classical
  obtain ⟨n, hn, hs⟩ := exists_safe_le h
  exact (Nat.find_min' (exists_safe h) hs).trans hn

noncomputable def nextRound (gen : FeedbackGenerator) (t : ℕ)
    (h : Fin t → Round) : Round := by
  classical
  let x := if Even t then 2 ^ (t / 2) else oddCode (freshIndex h)
  let xs : Fin (t + 1) → ℕ := Fin.snoc (fun i => (h i).presentation) x
  let oldAnswers : Fin t → Option Bool := fun i => (h i).answer
  let q := gen.query t xs oldAnswers
  let a := q.map fun z => membershipAnswer
    (core ∪ Set.range fun i : Fin (t + 1) => xs i) z
  let answers : Fin (t + 1) → Option Bool := Fin.snoc oldAnswers a
  exact ⟨x, q, a, gen.output t xs answers⟩

noncomputable def history (gen : FeedbackGenerator) :
    (t : ℕ) → Fin t → Round
  | 0 => Fin.elim0
  | t + 1 => Fin.snoc (history gen t) (nextRound gen t (history gen t))

noncomputable def round (gen : FeedbackGenerator) (t : ℕ) : Round :=
  history gen (t + 1) (Fin.last t)

theorem history_eq_round (gen : FeedbackGenerator) (t : ℕ) :
    ∀ i : Fin t, history gen t i = round gen i := by
  induction t with
  | zero => intro i; exact Fin.elim0 i
  | succ t ih =>
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rfl
      · simpa [history, round] using ih j

noncomputable def builtTranscript (gen : FeedbackGenerator) : Transcript where
  presentation t := (round gen t).presentation
  query t := (round gen t).query
  answer t := (round gen t).answer
  output t := (round gen t).output

theorem nextRound_eq_round (gen : FeedbackGenerator) (t : ℕ) :
    nextRound gen t (history gen t) = round gen t := by
  simp [round, history]


theorem round_presentation (gen : FeedbackGenerator) (t : ℕ) :
    (round gen t).presentation =
      if Even t then 2 ^ (t / 2) else oddCode (freshIndex (history gen t)) := by
  rw [← nextRound_eq_round]
  simp [nextRound]

theorem snoc_presentation (gen : FeedbackGenerator) (t : ℕ) :
    Fin.snoc (fun i : Fin t => (history gen t i).presentation)
      (if Even t then 2 ^ (t / 2) else oddCode (freshIndex (history gen t))) =
      fun i : Fin (t + 1) => (round gen i).presentation := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [round_presentation]
  · simp [history_eq_round]

theorem round_query (gen : FeedbackGenerator) (t : ℕ) :
    (round gen t).query = gen.query t
      (fun i => (round gen i).presentation)
      (fun i => (round gen i).answer) := by
  rw [← nextRound_eq_round]
  simp only [nextRound]
  rw [snoc_presentation]
  congr 1
  funext i
  simp [history_eq_round]

theorem round_answer (gen : FeedbackGenerator) (t : ℕ) :
    (round gen t).answer = (round gen t).query.map fun z =>
      membershipAnswer
        (core ∪ Set.range fun i : Fin (t + 1) => (round gen i).presentation) z := by
  rw [← nextRound_eq_round]
  simp only [nextRound]
  rw [snoc_presentation]

theorem snoc_answer (gen : FeedbackGenerator) (t : ℕ) :
    Fin.snoc (fun i : Fin t => (history gen t i).answer)
      ((round gen t).query.map fun z => membershipAnswer
        (core ∪ Set.range fun i : Fin (t + 1) => (round gen i).presentation) z) =
      fun i : Fin (t + 1) => (round gen i).answer := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [round_answer]
  · simp [history_eq_round]

theorem round_output (gen : FeedbackGenerator) (t : ℕ) :
    (round gen t).output = gen.output t
      (fun i => (round gen i).presentation)
      (fun i => (round gen i).answer) := by
  rw [← nextRound_eq_round]
  simp only [nextRound]
  rw [snoc_presentation]
  have hq : gen.query t (fun i => (round gen i).presentation)
      (fun i => (history gen t i).answer) = (round gen t).query := by
    rw [round_query]
    congr 1
    funext i
    simp [history_eq_round]
  rw [hq]
  rw [snoc_answer]

def admitted (gen : FeedbackGenerator) : Language :=
  Set.range fun r => (round gen (2 * r + 1)).presentation

def builtTarget (gen : FeedbackGenerator) : Language := core ∪ admitted gen

theorem presentation_even (gen : FeedbackGenerator) (r : ℕ) :
    (round gen (2 * r)).presentation = 2 ^ r := by
  rw [round_presentation]
  simp [show Even (2 * r) from ⟨r, by omega⟩]

theorem presentation_odd (gen : FeedbackGenerator) (r : ℕ) :
    (round gen (2 * r + 1)).presentation =
      oddCode (freshIndex (history gen (2 * r + 1))) := by
  rw [round_presentation]
  simp [show ¬Even (2 * r + 1) from Nat.not_even_iff_odd.mpr ⟨r, by omega⟩]

theorem presentation_mem_target (gen : FeedbackGenerator) (t : ℕ) :
    (builtTranscript gen).presentation t ∈ builtTarget gen := by
  rcases Nat.even_or_odd t with ht | ht
  · obtain ⟨r, rfl⟩ := ht
    left
    exact ⟨r, by simpa [builtTranscript, show r + r = 2 * r by omega] using (presentation_even gen r).symm⟩
  · obtain ⟨r, rfl⟩ := ht
    right
    exact ⟨r, rfl⟩


theorem odd_avoids_prior (gen : FeedbackGenerator) (r t : ℕ)
    (ht : t < 2 * r + 1) :
    (round gen (2 * r + 1)).presentation ≠ (round gen t).presentation ∧
    (round gen (2 * r + 1)).presentation ≠ (round gen t).output ∧
    (round gen t).query ≠ some (round gen (2 * r + 1)).presentation := by
  rw [presentation_odd]
  have hs := freshIndex_safe (history gen (2 * r + 1))
    ⟨t, ht⟩
  simpa [history_eq_round] using hs

theorem admitted_subset_ordinary (gen : FeedbackGenerator) :
    admitted gen ⊆ ordinary := by
  rintro z ⟨r, rfl⟩
  change (round gen (2 * r + 1)).presentation ∉ core
  rw [presentation_odd]
  exact oddCode_not_core _

theorem builtTarget_mem_class (gen : FeedbackGenerator) :
    builtTarget gen ∈ targetClass := by
  exact ⟨admitted gen, admitted_subset_ordinary gen, rfl⟩

theorem presentation_injective (gen : FeedbackGenerator) :
    Function.Injective (builtTranscript gen).presentation := by
  intro s t hst
  rcases Nat.even_or_odd s with ⟨a, rfl⟩ | ⟨a, rfl⟩ <;>
    rcases Nat.even_or_odd t with ⟨b, rfl⟩ | ⟨b, rfl⟩
  · change (round gen (a + a)).presentation = (round gen (b + b)).presentation at hst
    have hp : 2 ^ a = 2 ^ b := by
      simpa [show a + a = 2 * a by omega, show b + b = 2 * b by omega,
        presentation_even] using hst
    have hab : a = b := by
      have := congrArg Nat.log2 hp
      simpa using this
    omega
  · change (round gen (a + a)).presentation =
      (round gen (2 * b + 1)).presentation at hst
    have hc : (round gen (2 * b + 1)).presentation ∉ core :=
      admitted_subset_ordinary gen ⟨b, rfl⟩
    apply False.elim
    apply hc
    rw [← hst]
    exact ⟨a, by simpa [show a + a = 2 * a by omega] using
      (presentation_even gen a).symm⟩
  · change (round gen (2 * a + 1)).presentation =
      (round gen (b + b)).presentation at hst
    have hc : (round gen (2 * a + 1)).presentation ∉ core :=
      admitted_subset_ordinary gen ⟨a, rfl⟩
    apply False.elim
    apply hc
    rw [hst]
    exact ⟨b, by simpa [show b + b = 2 * b by omega] using
      (presentation_even gen b).symm⟩
  · change (round gen (2 * a + 1)).presentation =
      (round gen (2 * b + 1)).presentation at hst
    by_contra hab
    rcases lt_or_gt_of_ne hab with hab | hba
    · exact (odd_avoids_prior gen b (2 * a + 1) (by omega)).1 hst.symm
    · exact (odd_avoids_prior gen a (2 * b + 1) (by omega)).1 hst

theorem presentation_complete (gen : FeedbackGenerator) :
    Complete (builtTranscript gen).presentation (builtTarget gen) := by
  intro z hz
  rcases hz with ⟨r, hr⟩ | ⟨r, hr⟩
  · refine ⟨2 * r, ?_⟩
    simpa [builtTranscript] using (presentation_even gen r).trans hr
  · refine ⟨2 * r + 1, ?_⟩
    simpa [builtTranscript] using hr

theorem presentation_clean (gen : FeedbackGenerator) :
    Clean (builtTranscript gen).presentation (builtTarget gen) :=
  presentation_mem_target gen


theorem query_membership_iff_prefix (gen : FeedbackGenerator) (t z : ℕ)
    (hq : (round gen t).query = some z) :
    z ∈ builtTarget gen ↔
      z ∈ core ∪ Set.range (fun i : Fin (t + 1) => (round gen i).presentation) := by
  constructor
  · rintro (hz | ⟨r, hr⟩)
    · exact Or.inl hz
    · by_cases hrt : 2 * r + 1 ≤ t
      · right
        refine ⟨⟨2 * r + 1, by omega⟩, ?_⟩
        exact hr
      · have hav := (odd_avoids_prior gen r t (by omega)).2.2
        exact False.elim (hav (hq.trans (congrArg some hr).symm))
  · rintro (hz | ⟨i, rfl⟩)
    · exact Or.inl hz
    · simpa [builtTranscript] using presentation_mem_target gen i

theorem answer_truthful (gen : FeedbackGenerator) (t : ℕ) :
    (round gen t).answer = match (round gen t).query with
      | none => none
      | some z => some (membershipAnswer (builtTarget gen) z) := by
  rw [round_answer]
  cases hq : (round gen t).query with
  | none => simp [hq]
  | some z =>
      simp only [hq, Option.map_some, Option.some.injEq]
      classical
      have hi := query_membership_iff_prefix gen t z hq
      by_cases hp : z ∈ core ∪ Set.range (fun i : Fin (t + 1) =>
          (round gen i).presentation)
      · have ht : z ∈ builtTarget gen := hi.mpr hp
        simp [membershipAnswer, hp, ht]
      · have ht : z ∉ builtTarget gen := fun hz => hp (hi.mp hz)
        simp [membershipAnswer, hp, ht]

theorem follows_protocol (gen : FeedbackGenerator) :
    FollowsProtocol gen (builtTarget gen) (builtTranscript gen) := by
  intro t
  refine ⟨?_, ?_, ?_⟩
  · simpa [builtTranscript] using round_query gen t
  · simpa [builtTranscript] using answer_truthful gen t
  · simpa [builtTranscript] using round_output gen t

noncomputable def builtPresenter (gen : FeedbackGenerator) : CausalPresenter where
  next t _ _ _ _ := (builtTranscript gen).presentation t

theorem presented_by (gen : FeedbackGenerator) :
    PresentedBy (builtPresenter gen) (builtTranscript gen) := by
  intro t
  rfl

theorem admitted_bound (gen : FeedbackGenerator) (r : ℕ) :
    (round gen (2 * r + 1)).presentation ≤ 12 * r + 9 := by
  rw [presentation_odd]
  unfold oddCode
  have h := freshIndex_le (history gen (2 * r + 1))
  omega

theorem core_infinite : core.Infinite := by
  exact Set.infinite_range_of_injective (Nat.pow_right_injective (by omega : 2 ≤ 2))

theorem builtTarget_infinite (gen : FeedbackGenerator) : (builtTarget gen).Infinite := by
  exact core_infinite.mono (fun _ hx => Or.inl hx)

noncomputable def orderedTarget (gen : FeedbackGenerator) : OrderedLanguage := by
  classical
  letI : Infinite ↥(builtTarget gen) := (builtTarget_infinite gen).to_subtype
  exact {
    carrier := builtTarget gen
    enumeration := Nat.orderEmbeddingOfSet (builtTarget gen)
    enumeration_injective := (Nat.orderEmbeddingOfSet (builtTarget gen)).injective
    range_enumeration := Nat.orderEmbeddingOfSet_range (builtTarget gen)
  }

theorem orderedTarget_strictMono (gen : FeedbackGenerator) :
    StrictMono (orderedTarget gen).enumeration := by
  classical
  letI : Infinite ↥(builtTarget gen) := (builtTarget_infinite gen).to_subtype
  exact (Nat.orderEmbeddingOfSet (builtTarget gen)).strictMono


theorem orderedTarget_enumeration_le (gen : FeedbackGenerator) (n : ℕ) :
    (orderedTarget gen).enumeration n ≤ 12 * n + 9 := by
  classical
  letI : Infinite ↥(builtTarget gen) := (builtTarget_infinite gen).to_subtype
  let e := Nat.Subtype.orderIsoOfNat (builtTarget gen)
  by_contra hle
  have hbig : 12 * n + 9 < (orderedTarget gen).enumeration n := by omega
  let f : Fin (n + 1) → Fin n := fun i =>
    ⟨e.symm ⟨(round gen (2 * (i : ℕ) + 1)).presentation,
      Or.inr ⟨(i : ℕ), rfl⟩⟩, by
        have hv : (round gen (2 * (i : ℕ) + 1)).presentation <
            (orderedTarget gen).enumeration n :=
          lt_of_le_of_lt ((admitted_bound gen (i : ℕ)).trans (by omega)) hbig
        have he : e (e.symm ⟨(round gen (2 * (i : ℕ) + 1)).presentation,
            Or.inr ⟨(i : ℕ), rfl⟩⟩) < e n := by
          simpa [e, orderedTarget] using hv
        exact (e.lt_iff_lt).mp he⟩
  have hf : Function.Injective f := by
    intro i j hij
    have hidx : (f i : ℕ) = (f j : ℕ) := congrArg Fin.val hij
    have hsub := congrArg e hidx
    have hp : (round gen (2 * (i : ℕ) + 1)).presentation =
        (round gen (2 * (j : ℕ) + 1)).presentation := by
      simpa [f, e] using congrArg Subtype.val hsub
    have ht : 2 * (i : ℕ) + 1 = 2 * (j : ℕ) + 1 :=
      presentation_injective gen hp
    apply Fin.ext
    omega
  have hc := Fintype.card_le_of_injective f hf
  simp at hc


noncomputable def coreExponent (z : ℕ) (hz : z ∈ core) : ℕ := Classical.choose hz

theorem pow_coreExponent (z : ℕ) (hz : z ∈ core) :
    2 ^ coreExponent z hz = z := Classical.choose_spec hz

theorem core_prefixCount_le (gen : FeedbackGenerator) (n : ℕ) :
    (orderedTarget gen).prefixCount core n ≤ Nat.log2 (12 * n + 9) + 1 := by
  classical
  let B := 12 * n + 9
  let S := (Finset.range n).filter fun i => (orderedTarget gen).enumeration i ∈ core
  let f : ↥S → Fin (Nat.log2 B + 1) := fun i => by
    have hi : (i : ℕ) < n := by
      simpa using (Finset.mem_filter.mp i.property).1
    have hcore : (orderedTarget gen).enumeration (i : ℕ) ∈ core :=
      (Finset.mem_filter.mp i.property).2
    have hmono : (orderedTarget gen).enumeration (i : ℕ) ≤
        (orderedTarget gen).enumeration n :=
      (orderedTarget_strictMono gen).monotone (by omega)
    have hval : (orderedTarget gen).enumeration (i : ℕ) ≤ B :=
      hmono.trans (by simpa [B] using orderedTarget_enumeration_le gen n)
    have hpow : 2 ^ coreExponent ((orderedTarget gen).enumeration (i : ℕ)) hcore ≤ B := by
      simpa [pow_coreExponent] using hval
    exact ⟨coreExponent ((orderedTarget gen).enumeration (i : ℕ)) hcore,
      by
        have hB : B ≠ 0 := by simp [B]
        have := (Nat.le_log2 hB).2 hpow
        omega⟩
  have hf : Function.Injective f := by
    intro i j hij
    have hexp : coreExponent ((orderedTarget gen).enumeration (i : ℕ))
          (Finset.mem_filter.mp i.property).2 =
        coreExponent ((orderedTarget gen).enumeration (j : ℕ))
          (Finset.mem_filter.mp j.property).2 := congrArg Fin.val hij
    have hval : (orderedTarget gen).enumeration (i : ℕ) =
        (orderedTarget gen).enumeration (j : ℕ) := by
      rw [← pow_coreExponent ((orderedTarget gen).enumeration (i : ℕ))
        (Finset.mem_filter.mp i.property).2,
        ← pow_coreExponent ((orderedTarget gen).enumeration (j : ℕ))
        (Finset.mem_filter.mp j.property).2,
        hexp]
    apply Subtype.ext
    exact (orderedTarget gen).enumeration_injective hval
  have hc := Fintype.card_le_of_injective f hf
  simpa [GenLimit.KleinbergWei.OrderedLanguage.prefixCount, S, B] using hc


theorem log2_linear_bound (n : ℕ) (hn : n ≠ 0) :
    Nat.log2 (12 * n + 9) + 1 ≤ 6 + Nat.log2 n := by
  have harg : 12 * n + 9 ≤ 32 * n := by omega
  have hlog : Nat.log2 (12 * n + 9) ≤ Nat.log2 (32 * n) := by
    simpa [Nat.log2_eq_log_two] using (Nat.log_mono_right harg :
      Nat.log 2 (12 * n + 9) ≤ Nat.log 2 (32 * n))
  have heq : Nat.log2 (32 * n) = Nat.log2 n + 5 := by
    rw [show 32 * n = 2 * (16 * n) by omega, Nat.log2_two_mul (by omega),
      show 16 * n = 2 * (8 * n) by omega, Nat.log2_two_mul (by omega),
      show 8 * n = 2 * (4 * n) by omega, Nat.log2_two_mul (by omega),
      show 4 * n = 2 * (2 * n) by omega, Nat.log2_two_mul (by omega),
      Nat.log2_two_mul hn]
  omega

theorem core_prefixRatio_le (gen : FeedbackGenerator) (n : ℕ) :
    (orderedTarget gen).prefixRatio core n ≤
      ((6 + Nat.log2 n : ℕ) : ℝ) / (n : ℝ) := by
  by_cases hn : n = 0
  · simp [hn]
  · unfold GenLimit.KleinbergWei.OrderedLanguage.prefixRatio
    simp only [hn, if_false]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
    exact_mod_cast (core_prefixCount_le gen n).trans (log2_linear_bound n hn)

theorem core_ratio_tendsto_zero (gen : FeedbackGenerator) :
    Tendsto ((orderedTarget gen).prefixRatio core) atTop (𝓝 0) := by
  apply squeeze_zero
  · exact (orderedTarget gen).prefixRatio_nonneg core
  · exact core_prefixRatio_le gen
  · simpa [add_comm] using GenLimit.tendsto_countingError_div 6

theorem core_upperDensity_zero (gen : FeedbackGenerator) :
    (orderedTarget gen).upperDensity core = 0 := by
  exact (core_ratio_tendsto_zero gen).limsup_eq


theorem scored_subset_core (gen : FeedbackGenerator) :
    scored (builtTarget gen) (builtTranscript gen).presentation
      (builtTranscript gen).output ⊆ core := by
  rintro z ⟨hz, t, hout, hnew⟩
  by_contra hzcore
  rcases hz with hzcore' | ⟨r, hr⟩
  · exact hzcore hzcore'
  · have ht : t < 2 * r + 1 := by
      by_contra hlt
      apply hnew
      refine ⟨2 * r + 1, by omega, ?_⟩
      simpa [builtTranscript] using hr
    have hav := (odd_avoids_prior gen r t ht).2.1
    apply hav
    change (round gen (2 * r + 1)).presentation = (round gen t).output
    change (round gen t).output = z at hout
    exact hr.trans hout.symm

theorem scored_upperDensity_zero (gen : FeedbackGenerator) :
    (orderedTarget gen).upperDensity
      (scored (builtTarget gen) (builtTranscript gen).presentation
        (builtTranscript gen).output) = 0 := by
  apply le_antisymm
  · exact ((orderedTarget gen).upperDensity_mono (scored_subset_core gen)).trans_eq
      (core_upperDensity_zero gen)
  · exact (orderedTarget gen).upperDensity_nonneg _

theorem faithful_negative_witness (gen : FeedbackGenerator) :
    FaithfulNegativeWitness gen (builtTarget gen) (builtPresenter gen)
      (builtTranscript gen) (orderedTarget gen) := by
  refine ⟨rfl, orderedTarget_strictMono gen, presented_by gen,
    follows_protocol gen, presentation_clean gen, presentation_injective gen,
    presentation_complete gen, ?_⟩
  exact scored_upperDensity_zero gen


def encodedTarget (A : Set ℕ) : Language := core ∪ oddCode '' A

theorem encodedTarget_mem_class (A : Set ℕ) : encodedTarget A ∈ targetClass := by
  refine ⟨oddCode '' A, ?_, rfl⟩
  rintro z ⟨n, hn, rfl⟩
  exact oddCode_not_core n

def encodedTargetSubtype (A : Set ℕ) : ↥targetClass :=
  ⟨encodedTarget A, encodedTarget_mem_class A⟩

theorem encodedTarget_injective : Function.Injective encodedTargetSubtype := by
  intro A B hab
  have hAB : encodedTarget A = encodedTarget B := by
    simpa [encodedTargetSubtype] using congrArg Subtype.val hab
  apply Set.ext
  intro n
  constructor
  · intro hn
    have hz : oddCode n ∈ encodedTarget A := Or.inr ⟨n, hn, rfl⟩
    have hzB : oddCode n ∈ encodedTarget B := by
      rw [← hAB]
      exact hz
    rcases hzB with hzcore | ⟨m, hm, heq⟩
    · exact False.elim (oddCode_not_core n hzcore)
    · have : m = n := oddCode_injective heq
      simpa [this] using hm
  · intro hn
    have hz : oddCode n ∈ encodedTarget B := Or.inr ⟨n, hn, rfl⟩
    have hzA : oddCode n ∈ encodedTarget A := by
      rw [hAB]
      exact hz
    rcases hzA with hzcore | ⟨m, hm, heq⟩
    · exact False.elim (oddCode_not_core n hzcore)
    · have : m = n := oddCode_injective heq
      simpa [this] using hm

theorem targetClass_not_countable : ¬ targetClass.Countable := by
  intro hcount
  letI : Countable ↥targetClass := hcount
  have hsets : Countable (Set ℕ) := encodedTarget_injective.countable
  exact GenLimit.UnionClosedness.powerSet_not_countable ℕ hsets

theorem uniform_generation : UniformlyGeneratableWithoutSamples := by
  refine ⟨fun t => 2 ^ t, Nat.pow_right_injective (by omega), 0, ?_⟩
  intro K hK t ht
  rcases hK with ⟨A, hA, rfl⟩
  exact Or.inl ⟨t, rfl⟩

theorem negative_claim : NegativeClaim := by
  intro gen hvalid
  refine ⟨builtTarget gen, builtTarget_mem_class gen, builtPresenter gen,
    builtTranscript gen, orderedTarget gen, ?_⟩
  exact faithful_negative_witness gen

end Stage3Proof

theorem stage3_result : Stage3S2B.MainClaim := by
  exact ⟨Stage3Proof.targetClass_not_countable, Stage3Proof.uniform_generation,
    Stage3Proof.negative_claim⟩
