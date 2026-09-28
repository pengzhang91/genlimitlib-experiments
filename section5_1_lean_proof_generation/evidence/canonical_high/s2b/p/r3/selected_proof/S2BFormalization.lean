import Stage3Model
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Countable
import Mathlib.Tactic

open Set Filter
open scoped Classical

namespace S2BProof

open Stage3S2B

structure History (t : ℕ) where
  presentation : Fin t → ℕ
  query : Fin t → Option ℕ
  answer : Fin t → Option Bool
  output : Fin t → ℕ

private def emptyHistory : History 0 where
  presentation := Fin.elim0
  query := Fin.elim0
  answer := Fin.elim0
  output := Fin.elim0

private def extendFin {α : Type} {t : ℕ} (f : Fin t → α) (a : α) : Fin (t + 1) → α :=
  Fin.lastCases a f

private noncomputable def banned {t : ℕ} (h : History t) : Finset ℕ := by
  classical
  exact (Finset.univ.image h.presentation) ∪
    ((Finset.univ.image (fun i => (h.query i).getD 0)) ∪ Finset.univ.image h.output)

private lemma oddCandidate_injective : Function.Injective (fun j : ℕ => 2 * j + 3) := by
  intro a b hab
  have hm : 2 * a = 2 * b := Nat.add_right_cancel hab
  exact Nat.eq_of_mul_eq_mul_left (by omega) hm

private lemma exists_unbanned {t : ℕ} (h : History t) :
    ∃ j : ℕ, 2 * j + 3 ∉ banned h := by
  classical
  by_contra hn
  push_neg at hn
  let f : Fin ((banned h).card + 1) → ℕ := fun i => 2 * (i : ℕ) + 3
  have hf : Function.Injective f := oddCandidate_injective.comp Fin.val_injective
  have hrange : Finset.univ.image f ⊆ banned h := by
    intro z hz
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hz
    rcases hz with ⟨i, rfl⟩
    exact hn i
  have hc := Finset.card_le_card hrange
  rw [Finset.card_image_of_injective _ hf, Finset.card_univ, Fintype.card_fin] at hc
  omega

private noncomputable def freshIndex {t : ℕ} (h : History t) : ℕ :=
  Nat.find (exists_unbanned h)

private lemma freshIndex_spec {t : ℕ} (h : History t) :
    2 * freshIndex h + 3 ∉ banned h :=
  Nat.find_spec (exists_unbanned h)

private noncomputable def choosePresentation {t : ℕ} (h : History t) : ℕ :=
  if Even t then 2 ^ (t / 2) else 2 * freshIndex h + 3

private noncomputable def step (gen : FeedbackGenerator) {t : ℕ} (h : History t) : History (t + 1) := by
  classical
  let x := choosePresentation h
  let xs := extendFin h.presentation x
  let q := gen.query t xs h.answer
  let a : Option Bool := q.map fun z => decide (z ∈ core ∨ ∃ i, xs i = z)
  let ans := extendFin h.answer a
  let y := gen.output t xs ans
  exact {
    presentation := xs
    query := extendFin h.query q
    answer := ans
    output := extendFin h.output y
  }

private noncomputable def history (gen : FeedbackGenerator) : (t : ℕ) → History t
  | 0 => emptyHistory
  | t + 1 => step gen (history gen t)

private noncomputable def playPresentation (gen : FeedbackGenerator) (t : ℕ) : ℕ :=
  (history gen (t + 1)).presentation (Fin.last t)

private noncomputable def playQuery (gen : FeedbackGenerator) (t : ℕ) : Option ℕ :=
  (history gen (t + 1)).query (Fin.last t)

private noncomputable def playAnswer (gen : FeedbackGenerator) (t : ℕ) : Option Bool :=
  (history gen (t + 1)).answer (Fin.last t)

private noncomputable def playOutput (gen : FeedbackGenerator) (t : ℕ) : ℕ :=
  (history gen (t + 1)).output (Fin.last t)

private lemma extendFin_castSucc {α : Type} {t : ℕ} (f : Fin t → α) (a : α) (i : Fin t) :
    extendFin f a i.castSucc = f i := by
  simp [extendFin]

private lemma extendFin_last {α : Type} {t : ℕ} (f : Fin t → α) (a : α) :
    extendFin f a (Fin.last t) = a := by
  simp [extendFin]

private lemma history_prefix (gen : FeedbackGenerator) : ∀ {s t : ℕ} (hst : s < t),
    (history gen t).presentation ⟨s, hst⟩ = playPresentation gen s ∧
    (history gen t).query ⟨s, hst⟩ = playQuery gen s ∧
    (history gen t).answer ⟨s, hst⟩ = playAnswer gen s ∧
    (history gen t).output ⟨s, hst⟩ = playOutput gen s := by
  intro s t hst
  induction t with
  | zero => omega
  | succ t ih =>
      by_cases h : s = t
      · subst s
        have hfin : (⟨t, hst⟩ : Fin (t + 1)) = Fin.last t := Fin.ext rfl
        rw [hfin]
        exact ⟨rfl, rfl, rfl, rfl⟩
      · have hlt : s < t := by omega
        let i : Fin t := ⟨s, hlt⟩
        have hfin : (⟨s, hst⟩ : Fin (t + 1)) = i.castSucc := Fin.ext rfl
        have hp := congrArg (history gen (t + 1)).presentation hfin
        have hq := congrArg (history gen (t + 1)).query hfin
        have ha := congrArg (history gen (t + 1)).answer hfin
        have hy := congrArg (history gen (t + 1)).output hfin
        have old := ih hlt
        constructor
        · calc
            (history gen (t + 1)).presentation ⟨s, hst⟩ =
                (history gen (t + 1)).presentation i.castSucc := hp
            _ = (history gen t).presentation i := by simp [history, step, extendFin]
            _ = playPresentation gen s := old.1
        constructor
        · calc
            (history gen (t + 1)).query ⟨s, hst⟩ =
                (history gen (t + 1)).query i.castSucc := hq
            _ = (history gen t).query i := by simp [history, step, extendFin]
            _ = playQuery gen s := old.2.1
        constructor
        · calc
            (history gen (t + 1)).answer ⟨s, hst⟩ =
                (history gen (t + 1)).answer i.castSucc := ha
            _ = (history gen t).answer i := by simp [history, step, extendFin]
            _ = playAnswer gen s := old.2.2.1
        · calc
            (history gen (t + 1)).output ⟨s, hst⟩ =
                (history gen (t + 1)).output i.castSucc := hy
            _ = (history gen t).output i := by simp [history, step, extendFin]
            _ = playOutput gen s := old.2.2.2

private lemma history_presentation_eq (gen : FeedbackGenerator) {t : ℕ} (i : Fin t) :
    (history gen t).presentation i = playPresentation gen i :=
  (history_prefix gen i.isLt).1

private lemma history_query_eq (gen : FeedbackGenerator) {t : ℕ} (i : Fin t) :
    (history gen t).query i = playQuery gen i :=
  (history_prefix gen i.isLt).2.1

private lemma history_answer_eq (gen : FeedbackGenerator) {t : ℕ} (i : Fin t) :
    (history gen t).answer i = playAnswer gen i :=
  (history_prefix gen i.isLt).2.2.1

private lemma history_output_eq (gen : FeedbackGenerator) {t : ℕ} (i : Fin t) :
    (history gen t).output i = playOutput gen i :=
  (history_prefix gen i.isLt).2.2.2

private noncomputable def playTranscript (gen : FeedbackGenerator) : Transcript where
  presentation := playPresentation gen
  query := playQuery gen
  answer := playAnswer gen
  output := playOutput gen

private noncomputable def playTarget (gen : FeedbackGenerator) : Language :=
  Set.range (playPresentation gen)

private noncomputable def playPresenter : CausalPresenter where
  next t xs qs _ ys :=
    choosePresentation { presentation := xs, query := qs, answer := fun _ => none, output := ys }

private lemma playPresentation_step (gen : FeedbackGenerator) (t : ℕ) :
    playPresentation gen t = choosePresentation (history gen t) := by
  simp [playPresentation, history, step, extendFin]

private lemma playQuery_step (gen : FeedbackGenerator) (t : ℕ) :
    playQuery gen t = gen.query t (fun i => playPresentation gen i)
      (fun i => playAnswer gen i) := by
  simp only [playQuery, history, step, extendFin_last]
  congr 1 <;> funext i
  · exact history_presentation_eq gen i
  · exact history_answer_eq gen i

private lemma playAnswer_step (gen : FeedbackGenerator) (t : ℕ) :
    playAnswer gen t = (playQuery gen t).map fun z =>
      decide (z ∈ core ∨ ∃ i : Fin (t + 1), (fun j => playPresentation gen j) i = z) := by
  simp only [playAnswer, history, step, extendFin_last]
  have hqraw : gen.query t
      (extendFin (history gen t).presentation (choosePresentation (history gen t)))
      (history gen t).answer = playQuery gen t := by
    rw [playQuery_step]
    congr 1 <;> funext i
    · simpa [extendFin] using history_presentation_eq gen i
    · exact history_answer_eq gen i
  rw [hqraw]
  congr 2
  funext z
  congr 1
  apply propext
  constructor
  · rintro (hz | ⟨i, hi⟩)
    · exact Or.inl hz
    · exact Or.inr ⟨i, by
        calc
          playPresentation gen i = (history gen (t + 1)).presentation i :=
            (history_presentation_eq gen i).symm
          _ = z := by simpa [extendFin] using hi⟩
  · rintro (hz | ⟨i, hi⟩)
    · exact Or.inl hz
    · exact Or.inr ⟨i, by
        calc
          extendFin (history gen t).presentation (choosePresentation (history gen t)) i =
              (history gen (t + 1)).presentation i := by rfl
          _ = playPresentation gen i := history_presentation_eq gen i
          _ = z := hi⟩

private lemma playOutput_step (gen : FeedbackGenerator) (t : ℕ) :
    playOutput gen t = gen.output t (fun i => playPresentation gen i)
      (fun i => playAnswer gen i) := by
  simp only [playOutput, history, step, extendFin_last]
  congr 1 <;> funext i
  · exact history_presentation_eq gen i
  · exact history_answer_eq gen i

private lemma core_at_even (gen : FeedbackGenerator) (r : ℕ) :
    playPresentation gen (2 * r) = 2 ^ r := by
  rw [playPresentation_step]
  simp [choosePresentation, show Even (2 * r) from ⟨r, by omega⟩]

private lemma odd_value (gen : FeedbackGenerator) (r : ℕ) :
    ∃ j, playPresentation gen (2 * r + 1) = 2 * j + 3 := by
  rw [playPresentation_step]
  simp [choosePresentation, show ¬ Even (2 * r + 1) from Nat.not_even_iff_odd.mpr ⟨r, by omega⟩]

private lemma odd_not_core (j : ℕ) : 2 * j + 3 ∉ core := by
  rintro ⟨k, hk⟩
  cases k with
  | zero => norm_num at hk
  | succ k =>
      have he : Even (2 ^ (k + 1)) := by
        refine ⟨2 ^ k, by ring⟩
      have ho : ¬ Even (2 * j + 3) := Nat.not_even_iff_odd.mpr ⟨j + 1, by omega⟩
      exact ho (hk ▸ he)

private lemma playTarget_mem_class (gen : FeedbackGenerator) : playTarget gen ∈ targetClass := by
  refine ⟨playTarget gen \ core, ?_, ?_⟩
  · intro z hz
    exact hz.2
  · ext z
    constructor
    · intro hz
      by_cases hc : z ∈ core
      · exact Or.inl hc
      · exact Or.inr ⟨hz, hc⟩
    · rintro (hc | ⟨hz, _⟩)
      · rcases hc with ⟨r, rfl⟩
        exact ⟨2 * r, core_at_even gen r⟩
      · exact hz

private lemma presentedBy_play (gen : FeedbackGenerator) :
    PresentedBy playPresenter (playTranscript gen) := by
  intro t
  change playPresentation gen t = _
  rw [playPresentation_step]
  simp only [playPresenter, playTranscript]
  have hp : (history gen t).presentation = (fun i : Fin t => playPresentation gen i.val) :=
    funext (history_presentation_eq gen)
  have hq : (history gen t).query = (fun i : Fin t => playQuery gen i.val) :=
    funext (history_query_eq gen)
  have hy : (history gen t).output = (fun i : Fin t => playOutput gen i.val) :=
    funext (history_output_eq gen)
  let publicHistory : History t :=
      { presentation := fun i => playPresentation gen i.val,
        query := fun i => playQuery gen i.val,
        answer := fun _ => none,
        output := fun i => playOutput gen i.val }
  have hb : banned (history gen t) = banned publicHistory := by
    simp [publicHistory, banned, hp, hq, hy]
  change choosePresentation (history gen t) = choosePresentation publicHistory
  simp only [choosePresentation]
  split <;> simp_all [freshIndex]

private lemma clean_play (gen : FeedbackGenerator) :
    Clean (playPresentation gen) (playTarget gen) := by
  intro t
  exact ⟨t, rfl⟩

private lemma complete_play (gen : FeedbackGenerator) :
    Complete (playPresentation gen) (playTarget gen) := by
  rintro z ⟨t, rfl⟩
  exact ⟨t, rfl⟩

private lemma banned_presentation {gen : FeedbackGenerator} {i t : ℕ} (hit : i < t) :
    playPresentation gen i ∈ banned (history gen t) := by
  classical
  have hi : (⟨i, hit⟩ : Fin t) ∈ (Finset.univ : Finset (Fin t)) := Finset.mem_univ _
  have hm : (history gen t).presentation ⟨i, hit⟩ ∈
      Finset.univ.image (history gen t).presentation := Finset.mem_image.2 ⟨_, hi, rfl⟩
  rw [history_presentation_eq gen] at hm
  exact Finset.mem_union_left _ hm

private lemma banned_query {gen : FeedbackGenerator} {i t z : ℕ} (hit : i < t)
    (hq : playQuery gen i = some z) : z ∈ banned (history gen t) := by
  classical
  have hi : (⟨i, hit⟩ : Fin t) ∈ (Finset.univ : Finset (Fin t)) := Finset.mem_univ _
  have hv : ((history gen t).query ⟨i, hit⟩).getD 0 = z := by
    rw [history_query_eq gen]
    simp [hq]
  have hm : z ∈ Finset.univ.image (fun j => ((history gen t).query j).getD 0) :=
    Finset.mem_image.2 ⟨_, hi, hv⟩
  exact Finset.mem_union_right _ (Finset.mem_union_left _ hm)

private lemma banned_output {gen : FeedbackGenerator} {i t : ℕ} (hit : i < t) :
    playOutput gen i ∈ banned (history gen t) := by
  classical
  have hi : (⟨i, hit⟩ : Fin t) ∈ (Finset.univ : Finset (Fin t)) := Finset.mem_univ _
  have hm : (history gen t).output ⟨i, hit⟩ ∈
      Finset.univ.image (history gen t).output := Finset.mem_image.2 ⟨_, hi, rfl⟩
  rw [history_output_eq gen] at hm
  exact Finset.mem_union_right _ (Finset.mem_union_right _ hm)

private lemma odd_fresh {gen : FeedbackGenerator} {t : ℕ} (ht : ¬ Even t) :
    playPresentation gen t ∉ banned (history gen t) := by
  rw [playPresentation_step]
  simp only [choosePresentation, if_neg ht]
  exact freshIndex_spec _

private lemma presentation_mem_core_iff_even (gen : FeedbackGenerator) (t : ℕ) :
    playPresentation gen t ∈ core ↔ Even t := by
  constructor
  · intro hc
    by_contra hn
    rw [playPresentation_step] at hc
    simp only [choosePresentation, if_neg hn] at hc
    exact odd_not_core _ hc
  · rintro ⟨r, hr⟩
    have ht : t = 2 * r := by omega
    subst t
    exact ⟨r, by simpa [two_mul] using (core_at_even gen r).symm⟩

private lemma play_ne_of_lt (gen : FeedbackGenerator) {i j : ℕ} (hlt : i < j) :
    playPresentation gen i ≠ playPresentation gen j := by
  intro hij
  by_cases hj : Even j
  · have hjc : playPresentation gen j ∈ core := (presentation_mem_core_iff_even gen j).2 hj
    by_cases hi : Even i
    · rcases hi with ⟨a, ha⟩
      rcases hj with ⟨b, hb⟩
      have hia : playPresentation gen i = 2 ^ a := by
        simpa [two_mul, ha] using core_at_even gen a
      have hjb : playPresentation gen j = 2 ^ b := by
        simpa [two_mul, hb] using core_at_even gen b
      have hab : a = b := Nat.pow_right_injective (by norm_num : 2 ≤ (2 : ℕ))
        (hia.symm.trans (hij.trans hjb))
      omega
    · have hic : playPresentation gen i ∉ core :=
        fun h => hi ((presentation_mem_core_iff_even gen i).1 h)
      exact hic (hij ▸ hjc)
  · exact odd_fresh hj (hij ▸ banned_presentation hlt)

private lemma injective_play (gen : FeedbackGenerator) : Function.Injective (playPresentation gen) := by
  intro i j hij
  rcases lt_trichotomy i j with hlt | heq | hgt
  · exact (play_ne_of_lt gen hlt hij).elim
  · exact heq
  · exact (play_ne_of_lt gen hgt hij.symm).elim

private lemma query_false_ne_future {gen : FeedbackGenerator} {t s z : ℕ}
    (hts : t < s) (hq : playQuery gen t = some z) (hnc : z ∉ core)
    (hnp : ∀ i : Fin (t + 1), playPresentation gen i.val ≠ z) :
    playPresentation gen s ≠ z := by
  intro hs
  have hsc : playPresentation gen s ∈ core ↔ Even s := presentation_mem_core_iff_even gen s
  have hso : ¬ Even s := by
    intro he
    exact hnc (hs ▸ hsc.2 he)
  exact odd_fresh hso (hs ▸ banned_query hts hq)

private lemma truthful_answer (gen : FeedbackGenerator) (t z : ℕ)
    (hq : playQuery gen t = some z) :
    membershipAnswer (playTarget gen) z = decide (z ∈ core ∨
      ∃ i : Fin (t + 1), playPresentation gen i.val = z) := by
  classical
  apply Bool.eq_iff_iff.mpr
  simp only [membershipAnswer, Bool.decide_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨s, hs⟩
    by_cases hc : z ∈ core
    · exact Or.inl hc
    · right
      by_contra hn
      push_neg at hn
      have hts : t < s := by
        by_contra hle
        have hsle : s ≤ t := by omega
        exact hn ⟨s, by omega⟩ hs
      exact query_false_ne_future hts hq hc hn hs
  · rintro (hc | ⟨i, hi⟩)
    · rcases hc with ⟨r, rfl⟩
      exact ⟨2 * r, core_at_even gen r⟩
    · exact ⟨i.val, hi⟩

private lemma followsProtocol_play (gen : FeedbackGenerator) :
    FollowsProtocol gen (playTarget gen) (playTranscript gen) := by
  intro t
  change playQuery gen t = gen.query t (fun i => playPresentation gen i.val)
      (fun i => playAnswer gen i.val) ∧
    playAnswer gen t = (match playQuery gen t with
      | none => none
      | some z => some (membershipAnswer (playTarget gen) z)) ∧
    playOutput gen t = gen.output t (fun i => playPresentation gen i.val)
      (fun i => playAnswer gen i.val)
  refine ⟨playQuery_step gen t, ?_, playOutput_step gen t⟩
  rw [playAnswer_step]
  cases hq : playQuery gen t with
  | none => simp
  | some z =>
      simp only [Option.map_some]
      simp [hq, truthful_answer gen t z hq]

private lemma scored_subset_core (gen : FeedbackGenerator) :
    scored (playTarget gen) (playPresentation gen) (playOutput gen) ⊆ core := by
  intro z hz
  rcases hz with ⟨⟨s, hs⟩, t, hy, hobs⟩
  by_contra hnc
  have hst : t < s := by
    by_contra hle
    apply hobs
    exact ⟨s, by omega, hs⟩
  have hso : ¬ Even s := by
    intro he
    exact hnc (hs ▸ (presentation_mem_core_iff_even gen s).2 he)
  exact odd_fresh hso (hs ▸ hy ▸ banned_output hst)

private lemma exists_unbanned_le {t : ℕ} (h : History t) :
    ∃ j ≤ (banned h).card, 2 * j + 3 ∉ banned h := by
  classical
  let candidates := Finset.univ.image
    (fun i : Fin ((banned h).card + 1) => 2 * (i : ℕ) + 3)
  have hcand : candidates.card = (banned h).card + 1 := by
    simpa [candidates] using
      Finset.card_image_of_injective
        (Finset.univ : Finset (Fin ((banned h).card + 1)))
        (oddCandidate_injective.comp Fin.val_injective)
  obtain ⟨z, hz, hzb⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := banned h) (t := candidates) (by simp [hcand])
  rcases Finset.mem_image.1 hz with ⟨i, _, rfl⟩
  exact ⟨i, by omega, hzb⟩

private lemma freshIndex_le_card {t : ℕ} (h : History t) :
    freshIndex h ≤ (banned h).card := by
  obtain ⟨j, hj, hfree⟩ := exists_unbanned_le h
  exact (Nat.find_min' (exists_unbanned h) hfree).trans hj

private lemma banned_card_le {t : ℕ} (h : History t) : (banned h).card ≤ 3 * t := by
  classical
  have hp : (Finset.univ.image h.presentation).card ≤ t := by
    simpa using Finset.card_image_le (s := (Finset.univ : Finset (Fin t)))
  have hq : (Finset.univ.image (fun i => (h.query i).getD 0)).card ≤ t := by
    simpa using Finset.card_image_le
      (s := (Finset.univ : Finset (Fin t)))
      (f := fun i => (h.query i).getD 0)
  have hy : (Finset.univ.image h.output).card ≤ t := by
    simpa using Finset.card_image_le
      (s := (Finset.univ : Finset (Fin t))) (f := h.output)
  unfold banned
  exact (Finset.card_union_le _ _).trans
    ((add_le_add hp ((Finset.card_union_le _ _).trans (add_le_add hq hy))).trans (by omega))

private lemma odd_presentation_bound (gen : FeedbackGenerator) (r : ℕ) :
    playPresentation gen (2 * r + 1) ≤ 12 * r + 9 := by
  have hodd : ¬ Even (2 * r + 1) :=
    Nat.not_even_iff_odd.mpr ⟨r, by omega⟩
  rw [playPresentation_step]
  simp only [choosePresentation, if_neg hodd]
  have h1 := freshIndex_le_card (history gen (2 * r + 1))
  have h2 := banned_card_le (history gen (2 * r + 1))
  omega

private lemma nth_target_bound (gen : FeedbackGenerator) (n : ℕ) :
    Nat.nth (fun z => z ∈ playTarget gen) n ≤ 12 * n + 9 := by
  classical
  let f : ℕ → ℕ := fun i => playPresentation gen (2 * i + 1)
  have hf : Function.Injective f := by
    intro i j hij
    apply Nat.eq_of_mul_eq_mul_left (by omega : 0 < 2)
    apply Nat.add_right_cancel
    exact injective_play gen hij
  have hsub : (Finset.range (n + 1)).image f ⊆
      (Finset.range (12 * n + 10)).filter (fun z => z ∈ playTarget gen) := by
    intro z hz
    rcases Finset.mem_image.1 hz with ⟨i, hi, rfl⟩
    have hin : i ≤ n := by
      rw [Finset.mem_range] at hi
      omega
    apply Finset.mem_filter.2
    constructor
    · apply Finset.mem_range.2
      exact (odd_presentation_bound gen i).trans_lt (by omega)
    · exact ⟨2 * i + 1, rfl⟩
  have hcount : n < Nat.count (fun z => z ∈ playTarget gen) (12 * n + 10) := by
    rw [Nat.count_eq_card_filter_range]
    have hc := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ hf, Finset.card_range] at hc
    omega
  exact Nat.le_of_lt_succ (by
    have := Nat.nth_lt_of_lt_count hcount
    omega)

private noncomputable def coreExponent (z : {z // z ∈ core}) : ℕ :=
  Nat.find z.property

private lemma coreExponent_spec (z : {z // z ∈ core}) :
    2 ^ coreExponent z = (z : ℕ) :=
  Nat.find_spec z.property

private lemma coreExponent_injective : Function.Injective coreExponent := by
  intro z w h
  apply Subtype.ext
  rw [← coreExponent_spec z, ← coreExponent_spec w, h]

private lemma exponent_lt_sqrt_bound {k M : ℕ} (h : 2 ^ k ≤ M) :
    k < 2 * Nat.sqrt M + 2 := by
  let a := k / 2
  have hdiv : 2 * a ≤ k := by
    simpa [a, Nat.mul_comm] using Nat.div_mul_le_self k 2
  have hklt : k < 2 * a + 2 := by
    have hmod := Nat.mod_lt k (by omega : 0 < 2)
    have hdecomp := Nat.div_add_mod k 2
    dsimp [a]
    omega
  have hpow : 2 ^ (2 * a) ≤ 2 ^ k :=
    Nat.pow_le_pow_right (by omega) hdiv
  have hsq : a ^ 2 ≤ M := by
    have hexp := Nat.two_mul_sq_add_one_le_two_pow_two_mul a
    omega
  have ha : a ≤ Nat.sqrt M := Nat.le_sqrt'.2 hsq
  omega

private lemma count_core_le_sqrt (M : ℕ) :
    Nat.count (fun z => z ∈ core) (M + 1) ≤ 2 * Nat.sqrt M + 2 := by
  classical
  let S := (Finset.range (M + 1)).filter (fun z => z ∈ core)
  let e : {z // z ∈ S} → Fin (2 * Nat.sqrt M + 2) := fun z =>
    ⟨coreExponent ⟨(z : ℕ), (Finset.mem_filter.1 z.property).2⟩, by
      apply exponent_lt_sqrt_bound
      calc
        2 ^ coreExponent ⟨(z : ℕ), (Finset.mem_filter.1 z.property).2⟩ =
            (z : ℕ) := coreExponent_spec _
        _ ≤ M := by
          have hz := (Finset.mem_filter.1 z.property).1
          rw [Finset.mem_range] at hz
          omega⟩
  have he : Function.Injective e := by
    intro z w h
    apply Subtype.ext
    have hc :
        (⟨z, (Finset.mem_filter.1 z.property).2⟩ : {x // x ∈ core}) =
        ⟨w, (Finset.mem_filter.1 w.property).2⟩ :=
      coreExponent_injective (Fin.ext_iff.mp h)
    exact congrArg (fun q : {x // x ∈ core} => (q : ℕ)) hc
  rw [Nat.count_eq_card_filter_range]
  change S.card ≤ 2 * Nat.sqrt M + 2
  rw [← Fintype.card_coe]
  simpa using Fintype.card_le_of_injective e he

private lemma target_infinite (gen : FeedbackGenerator) : (playTarget gen).Infinite := by
  exact Set.infinite_range_of_injective (injective_play gen)

private noncomputable def orderedTarget (gen : FeedbackGenerator) : OrderedLanguage where
  carrier := playTarget gen
  enumeration := Nat.nth (fun z => z ∈ playTarget gen)
  enumeration_injective := Nat.nth_injective (target_infinite gen)
  range_enumeration := Nat.range_nth_of_infinite (target_infinite gen)

private lemma orderedTarget_inherits (gen : FeedbackGenerator) :
    InheritsAmbientOrder (orderedTarget gen) :=
  Nat.nth_strictMono (target_infinite gen)

private lemma prefixCount_core_le (gen : FeedbackGenerator) (n : ℕ) :
    (orderedTarget gen).prefixCount core n ≤
      Nat.count (fun z => z ∈ core) (12 * n + 10) := by
  classical
  let S := (Finset.range n).filter
    (fun i => (orderedTarget gen).enumeration i ∈ core)
  have hsub : S.image (orderedTarget gen).enumeration ⊆
      (Finset.range (12 * n + 10)).filter (fun z => z ∈ core) := by
    intro z hz
    rcases Finset.mem_image.1 hz with ⟨i, hi, rfl⟩
    have hiltn : i < n := by
      exact Finset.mem_range.1 (Finset.mem_filter.1 hi).1
    have hicore : (orderedTarget gen).enumeration i ∈ core :=
      (Finset.mem_filter.1 hi).2
    apply Finset.mem_filter.2
    refine ⟨Finset.mem_range.2 ?_, hicore⟩
    change Nat.nth (fun z => z ∈ playTarget gen) i < 12 * n + 10
    have hibound := nth_target_bound gen i
    omega
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ (orderedTarget gen).enumeration_injective] at hc
  simpa [GenLimit.KleinbergWei.OrderedLanguage.prefixCount,
    Nat.count_eq_card_filter_range, S] using hc

private lemma prefixCount_core_sq_le (gen : FeedbackGenerator) {n : ℕ} (hn : 1 ≤ n) :
    ((orderedTarget gen).prefixCount core n) ^ 2 ≤ 256 * n := by
  let c := (orderedTarget gen).prefixCount core n
  let M := 12 * n + 9
  have hc1 : c ≤ Nat.count (fun z => z ∈ core) (M + 1) := by
    simpa [c, M, Nat.add_assoc] using prefixCount_core_le gen n
  have hc2 : Nat.count (fun z => z ∈ core) (M + 1) ≤ 2 * Nat.sqrt M + 2 :=
    count_core_le_sqrt M
  have hsquare := Nat.sqrt_le M
  have hsle : Nat.sqrt M ≤ M := Nat.sqrt_le_self M
  dsimp [c, M] at *
  nlinarith

private lemma prefixRatio_core_tendsto_zero (gen : FeedbackGenerator) :
    Tendsto ((orderedTarget gen).prefixRatio core) atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (256 / ε ^ 2 : ℝ)
  refine ⟨max 1 N, ?_⟩
  intro n hn
  have hn1 : 1 ≤ n := le_trans (le_max_left 1 N) hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn1)
  have hsqNat := prefixCount_core_sq_le gen hn1
  have hsq : (((orderedTarget gen).prefixCount core n : ℕ) : ℝ) ^ 2 ≤
      256 * (n : ℝ) := by exact_mod_cast hsqNat
  have hratio_nonneg : 0 ≤ (orderedTarget gen).prefixRatio core n := by
    simp [GenLimit.KleinbergWei.OrderedLanguage.prefixRatio,
      Nat.ne_of_gt (Nat.zero_lt_of_lt hn1), div_nonneg]
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hratio_nonneg]
  rw [GenLimit.KleinbergWei.OrderedLanguage.prefixRatio,
    if_neg (Nat.ne_of_gt (Nat.zero_lt_of_lt hn1))]
  by_contra hnot
  have hge : ε ≤ (((orderedTarget gen).prefixCount core n : ℕ) : ℝ) / n :=
    le_of_not_gt hnot
  have hmul : ε * (n : ℝ) ≤ ((orderedTarget gen).prefixCount core n : ℕ) :=
    (le_div_iff₀ hnpos).mp hge
  have hmul_sq : (ε * (n : ℝ)) ^ 2 ≤
      (((orderedTarget gen).prefixCount core n : ℕ) : ℝ) ^ 2 := by
    apply (sq_le_sq₀ (mul_nonneg hε.le hnpos.le) (by positivity)).2
    exact hmul
  have hN' : (256 : ℝ) < ε ^ 2 * n := by
    have hepsq : 0 < ε ^ 2 := sq_pos_of_pos hε
    have hNle : N ≤ n := le_trans (le_max_right 1 N) hn
    have hcast : (N : ℝ) ≤ n := by exact_mod_cast hNle
    have := (div_lt_iff₀ hepsq).mp hN
    nlinarith
  nlinarith

private lemma prefixCount_mono (K : OrderedLanguage) {A B : Language}
    (hAB : A ⊆ B) (n : ℕ) :
    K.prefixCount A n ≤ K.prefixCount B n := by
  classical
  unfold GenLimit.KleinbergWei.OrderedLanguage.prefixCount
  apply Finset.card_le_card
  intro i hi
  rw [Finset.mem_filter] at hi ⊢
  exact ⟨hi.1, hAB hi.2⟩

private lemma prefixRatio_scored_tendsto_zero (gen : FeedbackGenerator) :
    Tendsto ((orderedTarget gen).prefixRatio
      (scored (playTarget gen) (playPresentation gen) (playOutput gen)))
      atTop (nhds 0) := by
  apply squeeze_zero
    (f := (orderedTarget gen).prefixRatio
      (scored (playTarget gen) (playPresentation gen) (playOutput gen)))
    (g := (orderedTarget gen).prefixRatio core)
  · intro n
    unfold GenLimit.KleinbergWei.OrderedLanguage.prefixRatio
    split <;> positivity
  · intro n
    by_cases hn : n = 0
    · simp [GenLimit.KleinbergWei.OrderedLanguage.prefixRatio, hn]
    · simp only [GenLimit.KleinbergWei.OrderedLanguage.prefixRatio, hn, if_false]
      have hc := prefixCount_mono (orderedTarget gen) (scored_subset_core gen) n
      exact div_le_div_of_nonneg_right (Nat.cast_le.2 hc) (by positivity)
  · exact prefixRatio_core_tendsto_zero gen

private lemma density_zero (gen : FeedbackGenerator) :
    (orderedTarget gen).upperDensity
      (scored (playTarget gen) (playPresentation gen) (playOutput gen)) = 0 := by
  unfold GenLimit.KleinbergWei.OrderedLanguage.upperDensity
  exact (prefixRatio_scored_tendsto_zero gen).limsup_eq

private noncomputable def classEmbedding (A : Set ℕ) : Language :=
  core ∪ ((fun n => 2 * n + 3) '' A)

private lemma classEmbedding_mem (A : Set ℕ) : classEmbedding A ∈ targetClass := by
  refine ⟨(fun n => 2 * n + 3) '' A, ?_, rfl⟩
  rintro z ⟨n, _, rfl⟩
  exact odd_not_core n

private lemma classEmbedding_injective : Function.Injective classEmbedding := by
  intro A B hab
  ext n
  have hn : 2 * n + 3 ∉ core := odd_not_core n
  have hA : 2 * n + 3 ∈ classEmbedding A ↔ n ∈ A := by
    simp only [classEmbedding, Set.mem_union, Set.mem_image]
    constructor
    · rintro (hc | ⟨m, hm, heq⟩)
      · exact (hn hc).elim
      · exact (oddCandidate_injective heq) ▸ hm
    · intro hm
      exact Or.inr ⟨n, hm, rfl⟩
  have hB : 2 * n + 3 ∈ classEmbedding B ↔ n ∈ B := by
    simp only [classEmbedding, Set.mem_union, Set.mem_image]
    constructor
    · rintro (hc | ⟨m, hm, heq⟩)
      · exact (hn hc).elim
      · exact (oddCandidate_injective heq) ▸ hm
    · intro hm
      exact Or.inr ⟨n, hm, rfl⟩
  constructor
  · intro hnA
    exact hB.mp (hab ▸ hA.mpr hnA)
  · intro hnB
    exact hA.mp (hab.symm ▸ hB.mpr hnB)

private lemma targetClass_uncountable : ¬ targetClass.Countable := by
  intro hc
  have hr : (Set.range classEmbedding).Countable := by
    apply hc.mono
    rintro K ⟨A, rfl⟩
    exact classEmbedding_mem A
  have hp := hr.preimage classEmbedding_injective
  have hu : classEmbedding ⁻¹' Set.range classEmbedding = (Set.univ : Set (Set ℕ)) := by
    ext A
    simp
  rw [hu] at hp
  obtain ⟨f, hf⟩ := hp.exists_surjective Set.univ_nonempty
  let D : Set ℕ := {n | n ∉ (f n : Set ℕ)}
  obtain ⟨n, hn⟩ := hf ⟨D, Set.mem_univ D⟩
  have hfn : (f n : Set ℕ) = D := congrArg Subtype.val hn
  have hdiag : n ∈ D ↔ n ∉ D := by
    change n ∉ (f n : Set ℕ) ↔ n ∉ D
    rw [hfn]
  by_cases h : n ∈ D
  · exact (hdiag.mp h) h
  · exact h (hdiag.mpr h)

private lemma uniform_positive : UniformlyGeneratableWithoutSamples := by
  refine ⟨fun t => 2 ^ t, Nat.pow_right_injective (by norm_num), 0, ?_⟩
  intro K hK t _
  rcases hK with ⟨A, hA, rfl⟩
  exact Or.inl ⟨t, rfl⟩

private lemma negative_claim : NegativeClaim := by
  intro gen _
  refine ⟨playTarget gen, playTarget_mem_class gen, playPresenter,
    playTranscript gen, orderedTarget gen, ?_⟩
  exact ⟨rfl, orderedTarget_inherits gen, presentedBy_play gen,
    followsProtocol_play gen, clean_play gen, injective_play gen,
    complete_play gen, density_zero gen⟩

theorem assembled_claim : MainClaim := by
  exact ⟨targetClass_uncountable, uniform_positive, negative_claim⟩

end S2BProof

theorem stage3_result : Stage3S2B.MainClaim := by
  exact S2BProof.assembled_claim
