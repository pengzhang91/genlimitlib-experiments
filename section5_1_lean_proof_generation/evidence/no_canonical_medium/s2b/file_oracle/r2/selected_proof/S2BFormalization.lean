import Stage3Model
import GenLimit.Paper39_DenseGeneration.Abstract.Density
import Mathlib.Data.Nat.Nth
import GenLimit.Paper10_UnionClosednessOfLanguageGeneration.Cardinality

open Set
open Stage3S2B

lemma ordinary_infinite : Infinite ordinary := by
  let f : ℕ → ℕ := fun n => 2 * n + 3
  have hf : Function.Injective f := by
    intro a b h
    simp only [f] at h
    omega
  have hr : Set.range f ⊆ ordinary := by
    intro z hz
    obtain ⟨n, rfl⟩ := hz
    intro hc
    obtain ⟨k, hk⟩ := hc
    change 2 ^ k = 2 * n + 3 at hk
    by_cases hk0 : k = 0
    · simp [hk0, f] at hk
    · have hodd : Odd (2 ^ k) := by
        rw [hk]
        exact ⟨n + 1, by simp [f]; omega⟩
      have heven : Even (2 ^ k) := (Nat.even_pow).2 ⟨by simp, hk0⟩
      exact (Nat.not_even_iff_odd.mpr hodd) heven
  exact Set.infinite_coe_iff.mpr
    (Set.infinite_of_injective_forall_mem hf (fun n => hr ⟨n, rfl⟩))

lemma targetClass_not_countable : ¬ targetClass.Countable := by
  intro h
  haveI : Infinite ordinary := ordinary_infinite
  have hp := GenLimit.UnionClosedness.powerSet_not_countable ordinary
  apply hp
  letI : Countable targetClass := h
  let embed : Set ordinary → targetClass := fun A =>
    ⟨core ∪ ((fun z : ordinary => (z : ℕ)) '' A), by
      refine ⟨(fun z : ordinary => (z : ℕ)) '' A, ?_, rfl⟩
      intro n hn
      obtain ⟨w, -, rfl⟩ := hn
      exact w.property⟩
  have hinj : Function.Injective embed := by
    intro A B hab
    apply Set.ext
    intro z
    have hnotcore : (z : ℕ) ∉ core := z.property
    have hmem (C : Set ordinary) :
        ((z : ℕ) ∈ core ∪ ((fun w : ordinary => (w : ℕ)) '' C)) ↔ z ∈ C := by
      simp [hnotcore]
    have hsets : (embed A : Set ℕ) = embed B := congrArg Subtype.val hab
    exact (hmem A).symm.trans ((Set.ext_iff.mp hsets (z : ℕ)).trans (hmem B))
  exact hinj.countable

lemma pow_two_injective : Function.Injective (fun k : ℕ => 2 ^ k) := by
  exact Nat.pow_right_injective (by omega)

lemma uniform_generation : UniformlyGeneratableWithoutSamples := by
  refine ⟨fun k => 2 ^ k, pow_two_injective, 0, ?_⟩
  intro K hK t ht
  obtain ⟨A, hA, rfl⟩ := hK
  exact Or.inl ⟨t, rfl⟩

namespace Adversary

structure Hist (n : ℕ) where
  x : Fin n → ℕ
  q : Fin n → Option ℕ
  a : Fin n → Option Bool
  y : Fin n → ℕ

def candidates (t : ℕ) : Finset ℕ :=
  (Finset.range (3 * t + 1)).image (fun j => 2 * j + 3)

def forbidden {t : ℕ} (h : Hist t) : Finset ℕ :=
  (Finset.univ.image h.x ∪ Finset.univ.image h.y) ∪
    Finset.univ.image (fun i => (h.q i).getD 0)

lemma candidates_card (t : ℕ) : (candidates t).card = 3 * t + 1 := by
  classical
  rw [candidates, Finset.card_image_of_injective]
  · simp
  · intro a b hab
    simp only at hab
    omega

lemma forbidden_card_le {t : ℕ} (h : Hist t) : (forbidden h).card ≤ 3 * t := by
  classical
  unfold forbidden
  calc
    ((Finset.univ.image h.x ∪ Finset.univ.image h.y) ∪
      Finset.univ.image (fun i => (h.q i).getD 0)).card
        ≤ (Finset.univ.image h.x ∪ Finset.univ.image h.y).card +
          (Finset.univ.image (fun i => (h.q i).getD 0)).card := Finset.card_union_le _ _
    _ ≤ ((Finset.univ.image h.x).card + (Finset.univ.image h.y).card) +
          (Finset.univ.image (fun i => (h.q i).getD 0)).card :=
      Nat.add_le_add_right (Finset.card_union_le _ _) _
    _ ≤ (t + t) + t := by
      have hx : (Finset.univ.image h.x).card ≤ t := by
        exact (Finset.card_image_le.trans_eq (Finset.card_fin t))
      have hy : (Finset.univ.image h.y).card ≤ t := by
        exact (Finset.card_image_le.trans_eq (Finset.card_fin t))
      have hq : (Finset.univ.image (fun i => (h.q i).getD 0)).card ≤ t := by
        exact (Finset.card_image_le.trans_eq (Finset.card_fin t))
      omega
    _ = 3 * t := by omega

lemma exists_fresh {t : ℕ} (h : Hist t) : ∃ z ∈ candidates t, z ∉ forbidden h := by
  classical
  have hc : (forbidden h).card < (candidates t).card := by
    rw [candidates_card]
    have := forbidden_card_le h
    omega
  exact Finset.exists_mem_not_mem_of_card_lt_card hc

noncomputable def fresh {t : ℕ} (h : Hist t) : ℕ := Classical.choose (exists_fresh h)

lemma fresh_mem_candidates {t : ℕ} (h : Hist t) : fresh h ∈ candidates t :=
  (Classical.choose_spec (exists_fresh h)).1

lemma fresh_not_forbidden {t : ℕ} (h : Hist t) : fresh h ∉ forbidden h :=
  (Classical.choose_spec (exists_fresh h)).2

lemma fresh_odd {t : ℕ} (h : Hist t) : Odd (fresh h) := by
  classical
  have hm := fresh_mem_candidates h
  rw [candidates, Finset.mem_image] at hm
  obtain ⟨j, hj, heq⟩ := hm
  rw [← heq]
  exact ⟨j + 1, by omega⟩

lemma fresh_gt_one {t : ℕ} (h : Hist t) : 1 < fresh h := by
  classical
  have hm := fresh_mem_candidates h
  rw [candidates, Finset.mem_image] at hm
  obtain ⟨j, hj, heq⟩ := hm
  omega

lemma fresh_not_core {t : ℕ} (h : Hist t) : fresh h ∈ ordinary := by
  intro hc
  obtain ⟨k, hk⟩ := hc
  change 2 ^ k = fresh h at hk
  by_cases hk0 : k = 0
  · simp [hk0] at hk
    exact (Nat.ne_of_gt (fresh_gt_one h)) hk.symm
  · have heven : Even (2 ^ k) := (Nat.even_pow).2 ⟨by simp, hk0⟩
    rw [hk] at heven
    exact (Nat.not_even_iff_odd.mpr (fresh_odd h)) heven

lemma fresh_ne_x {t : ℕ} (h : Hist t) (i : Fin t) : fresh h ≠ h.x i := by
  intro heq
  apply fresh_not_forbidden h
  simp [forbidden, heq]

lemma fresh_ne_y {t : ℕ} (h : Hist t) (i : Fin t) : fresh h ≠ h.y i := by
  intro heq
  apply fresh_not_forbidden h
  simp [forbidden, heq]

lemma fresh_ne_q {t : ℕ} (h : Hist t) (i : Fin t) (hq : h.q i = some (fresh h)) : False := by
  apply fresh_not_forbidden h
  have hget : (h.q i).getD 0 = fresh h := by simp [hq]
  unfold forbidden
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
  exact Or.inr ⟨i, hget⟩

noncomputable def truthValue (P : Prop) : Bool := by
  classical
  exact decide P

noncomputable def nextX {t : ℕ} (h : Hist t) : ℕ :=
  if ht : Even t then 2 ^ (t / 2) else fresh h

noncomputable def step (gen : FeedbackGenerator) {t : ℕ} (h : Hist t) : Hist (t + 1) := by
  classical
  let xnew := nextX h
  let xv : Fin (t + 1) → ℕ := Fin.lastCases xnew h.x
  let qnew := gen.query t xv h.a
  let qv : Fin (t + 1) → Option ℕ := Fin.lastCases qnew h.q
  let anew : Option Bool := match qnew with
    | none => none
    | some z => some (truthValue (z ∈ core ∨ ∃ i : Fin (t + 1), xv i = z))
  let av : Fin (t + 1) → Option Bool := Fin.lastCases anew h.a
  let ynew := gen.output t xv av
  let yv : Fin (t + 1) → ℕ := Fin.lastCases ynew h.y
  exact ⟨xv, qv, av, yv⟩

noncomputable def histories (gen : FeedbackGenerator) : (t : ℕ) → Hist t
  | 0 => ⟨Fin.elim0, Fin.elim0, Fin.elim0, Fin.elim0⟩
  | t + 1 => step gen (histories gen t)

lemma histories_succ_x (gen : FeedbackGenerator) (t : ℕ) (i : Fin t) :
    (histories gen (t + 1)).x i.castSucc = (histories gen t).x i := by
  simp [histories, step]

lemma histories_succ_q (gen : FeedbackGenerator) (t : ℕ) (i : Fin t) :
    (histories gen (t + 1)).q i.castSucc = (histories gen t).q i := by
  simp [histories, step]

lemma histories_succ_a (gen : FeedbackGenerator) (t : ℕ) (i : Fin t) :
    (histories gen (t + 1)).a i.castSucc = (histories gen t).a i := by
  simp [histories, step]

lemma histories_succ_y (gen : FeedbackGenerator) (t : ℕ) (i : Fin t) :
    (histories gen (t + 1)).y i.castSucc = (histories gen t).y i := by
  simp [histories, step]

noncomputable def transcript (gen : FeedbackGenerator) : Transcript where
  presentation t := (histories gen (t + 1)).x (Fin.last t)
  query t := (histories gen (t + 1)).q (Fin.last t)
  answer t := (histories gen (t + 1)).a (Fin.last t)
  output t := (histories gen (t + 1)).y (Fin.last t)

lemma transcript_x_hist (gen : FeedbackGenerator) (t : ℕ) :
    (fun i : Fin t => (transcript gen).presentation i) = (histories gen t).x := by
  induction t with
  | zero => funext i; exact Fin.elim0 i
  | succ t ih =>
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rfl
      · rw [histories_succ_x]
        exact congrFun ih j

lemma transcript_q_hist (gen : FeedbackGenerator) (t : ℕ) :
    (fun i : Fin t => (transcript gen).query i) = (histories gen t).q := by
  induction t with
  | zero => funext i; exact Fin.elim0 i
  | succ t ih =>
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rfl
      · rw [histories_succ_q]
        exact congrFun ih j

lemma transcript_a_hist (gen : FeedbackGenerator) (t : ℕ) :
    (fun i : Fin t => (transcript gen).answer i) = (histories gen t).a := by
  induction t with
  | zero => funext i; exact Fin.elim0 i
  | succ t ih =>
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rfl
      · rw [histories_succ_a]
        exact congrFun ih j

lemma transcript_y_hist (gen : FeedbackGenerator) (t : ℕ) :
    (fun i : Fin t => (transcript gen).output i) = (histories gen t).y := by
  induction t with
  | zero => funext i; exact Fin.elim0 i
  | succ t ih =>
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rfl
      · rw [histories_succ_y]
        exact congrFun ih j

end Adversary

namespace Adversary

lemma presentation_eq_nextX (gen : FeedbackGenerator) (t : ℕ) :
    (transcript gen).presentation t = nextX (histories gen t) := by
  simp [transcript, histories, step]

lemma query_eq_gen (gen : FeedbackGenerator) (t : ℕ) :
    (transcript gen).query t = gen.query t
      (fun i => (transcript gen).presentation i)
      (fun i => (transcript gen).answer i) := by
  rw [transcript_x_hist, transcript_a_hist]
  simp [transcript, histories, step]

lemma output_eq_gen (gen : FeedbackGenerator) (t : ℕ) :
    (transcript gen).output t = gen.output t
      (fun i => (transcript gen).presentation i)
      (fun i => (transcript gen).answer i) := by
  have hx := transcript_x_hist gen (t + 1)
  have ha := transcript_a_hist gen (t + 1)
  rw [hx, ha]
  simp [transcript, histories, step]

lemma presentation_even (gen : FeedbackGenerator) (k : ℕ) :
    (transcript gen).presentation (2 * k) = 2 ^ k := by
  rw [presentation_eq_nextX]
  simp [nextX, show Even (2 * k) by exact ⟨k, by omega⟩]

lemma presentation_odd (gen : FeedbackGenerator) (k : ℕ) :
    (transcript gen).presentation (2 * k + 1) = fresh (histories gen (2 * k + 1)) := by
  rw [presentation_eq_nextX]
  have hnot : ¬ Even (2 * k + 1) := Nat.not_even_iff_odd.mpr ⟨k, by omega⟩
  simp [nextX, hnot]

lemma presentation_mem_core_or_ordinary (gen : FeedbackGenerator) (t : ℕ) :
    (transcript gen).presentation t ∈ core ∨
      (transcript gen).presentation t ∈ ordinary := by
  by_cases ht : Even t
  · left
    rw [presentation_eq_nextX]
    simp only [nextX, dif_pos ht]
    exact ⟨t / 2, rfl⟩
  · right
    rw [presentation_eq_nextX]
    simp [nextX, ht, fresh_not_core]

lemma core_subset_range (gen : FeedbackGenerator) :
    core ⊆ Set.range (transcript gen).presentation := by
  intro z hz
  obtain ⟨k, rfl⟩ := hz
  exact ⟨2 * k, presentation_even gen k⟩

lemma target_mem_class (gen : FeedbackGenerator) :
    Set.range (transcript gen).presentation ∈ targetClass := by
  let K := Set.range (transcript gen).presentation
  let A := K ∩ ordinary
  refine ⟨A, Set.inter_subset_right, ?_⟩
  apply Set.Subset.antisymm
  · intro z hz
    obtain ⟨t, rfl⟩ := hz
    rcases presentation_mem_core_or_ordinary gen t with hc | ho
    · exact Or.inl hc
    · exact Or.inr ⟨⟨t, rfl⟩, ho⟩
  · intro z hz
    rcases hz with hz | hz
    · exact core_subset_range gen hz
    · exact hz.1

lemma future_odd_ne_past_x (gen : FeedbackGenerator) {r s : ℕ}
    (hrs : r < 2 * s + 1) :
    (transcript gen).presentation (2 * s + 1) ≠ (transcript gen).presentation r := by
  rw [presentation_odd]
  have hhist := congrFun (transcript_x_hist gen (2 * s + 1))
    ⟨r, by omega⟩
  rw [hhist]
  exact fresh_ne_x _ ⟨r, by omega⟩

lemma future_odd_ne_past_y (gen : FeedbackGenerator) {r s : ℕ}
    (hrs : r < 2 * s + 1) :
    (transcript gen).presentation (2 * s + 1) ≠ (transcript gen).output r := by
  rw [presentation_odd]
  have hhist := congrFun (transcript_y_hist gen (2 * s + 1))
    ⟨r, by omega⟩
  rw [hhist]
  exact fresh_ne_y _ ⟨r, by omega⟩

lemma future_odd_ne_past_q (gen : FeedbackGenerator) {r s : ℕ}
    (hrs : r < 2 * s + 1)
    (hq : (transcript gen).query r = some ((transcript gen).presentation (2 * s + 1))) : False := by
  rw [presentation_odd] at hq
  have hhist := congrFun (transcript_q_hist gen (2 * s + 1))
    ⟨r, by omega⟩
  rw [hhist] at hq
  exact fresh_ne_q _ ⟨r, by omega⟩ hq

lemma presentation_ne_of_lt (gen : FeedbackGenerator) {r s : ℕ} (hrs : r < s) :
    (transcript gen).presentation r ≠ (transcript gen).presentation s := by
  intro heq
  rcases Nat.even_or_odd s with hseven | hsodd
  · rcases Nat.even_or_odd r with hreven | hrodd
    · have hrform : r = 2 * (r / 2) := by
        obtain ⟨j, hj⟩ := hreven
        omega
      have hsform : s = 2 * (s / 2) := by
        obtain ⟨j, hj⟩ := hseven
        omega
      rw [hrform, hsform, presentation_even, presentation_even] at heq
      have hhalf := pow_two_injective heq
      omega
    · have hrord : (transcript gen).presentation r ∈ ordinary := by
        rw [presentation_eq_nextX]
        simp [nextX, Nat.not_even_iff_odd.mpr hrodd, fresh_not_core]
      have hscore : (transcript gen).presentation s ∈ core := by
        rw [presentation_eq_nextX]
        simp only [nextX, dif_pos hseven]
        exact ⟨s / 2, rfl⟩
      exact hrord (heq ▸ hscore)
  · obtain ⟨k, hk⟩ := hsodd
    have hsform : s = 2 * k + 1 := by omega
    subst s
    exact future_odd_ne_past_x gen hrs heq.symm

lemma presentation_injective (gen : FeedbackGenerator) :
    Function.Injective (transcript gen).presentation := by
  intro r s hrs
  rcases lt_trichotomy r s with hlt | heq | hgt
  · exact (presentation_ne_of_lt gen hlt hrs).elim
  · exact heq
  · exact (presentation_ne_of_lt gen hgt hrs.symm).elim

lemma target_clean (gen : FeedbackGenerator) :
    Clean (transcript gen).presentation (Set.range (transcript gen).presentation) := by
  intro t
  exact ⟨t, rfl⟩

lemma target_complete (gen : FeedbackGenerator) :
    Complete (transcript gen).presentation (Set.range (transcript gen).presentation) := by
  intro z hz
  exact hz

lemma query_mem_target_iff (gen : FeedbackGenerator) (t z : ℕ)
    (hq : (transcript gen).query t = some z) :
    z ∈ Set.range (transcript gen).presentation ↔
      z ∈ core ∨ z ∈ observedThrough (transcript gen).presentation t := by
  constructor
  · rintro ⟨s, rfl⟩
    by_cases hst : s ≤ t
    · exact Or.inr ⟨s, hst, rfl⟩
    · rcases presentation_mem_core_or_ordinary gen s with hc | ho
      · exact Or.inl hc
      · have hsodd : Odd s := Nat.not_even_iff_odd.mp (by
          intro hseven
          rw [presentation_eq_nextX, nextX, dif_pos hseven] at ho
          exact ho ⟨s / 2, rfl⟩)
        obtain ⟨k, hk⟩ := hsodd
        have hsform : s = 2 * k + 1 := by omega
        subst s
        exact (future_odd_ne_past_q gen (by omega) hq).elim
  · rintro (hc | ho)
    · exact core_subset_range gen hc
    · obtain ⟨s, hst, hs⟩ := ho
      exact ⟨s, hs⟩

lemma answer_eq_internal (gen : FeedbackGenerator) (t : ℕ) :
    (transcript gen).answer t =
      match gen.query t (histories gen (t + 1)).x (histories gen t).a with
      | none => none
      | some z => some (truthValue (z ∈ core ∨ ∃ i : Fin (t + 1),
          (histories gen (t + 1)).x i = z)) := by
  simp [transcript, histories, step]

lemma answer_eq_rule (gen : FeedbackGenerator) (t : ℕ) :
    (transcript gen).answer t = match (transcript gen).query t with
      | none => none
      | some z => some (truthValue (z ∈ core ∨ z ∈ observedThrough (transcript gen).presentation t)) := by
  classical
  rw [answer_eq_internal, query_eq_gen, transcript_x_hist, transcript_a_hist]
  split
  · rfl
  · rename_i z hz
    congr 2
    apply propext
    constructor
    · rintro (hc | ⟨i, hi⟩)
      · exact Or.inl hc
      · exact Or.inr ⟨i, by omega, (congrFun (transcript_x_hist gen (t + 1)) i).trans hi⟩
    · rintro (hc | ⟨r, hrt, hr⟩)
      · exact Or.inl hc
      · right
        let i : Fin (t + 1) := ⟨r, by omega⟩
        exact ⟨i, (congrFun (transcript_x_hist gen (t + 1)) i).symm.trans hr⟩

lemma answer_eq_membership (gen : FeedbackGenerator) (t : ℕ) :
    (transcript gen).answer t = match (transcript gen).query t with
      | none => none
      | some z => some (membershipAnswer (Set.range (transcript gen).presentation) z) := by
  classical
  rw [answer_eq_rule]
  split
  · rfl
  · rename_i z hq
    unfold membershipAnswer truthValue
    rw [query_mem_target_iff gen t z hq]

lemma follows_protocol (gen : FeedbackGenerator) :
    FollowsProtocol gen (Set.range (transcript gen).presentation) (transcript gen) := by
  intro t
  exact ⟨query_eq_gen gen t, answer_eq_membership gen t, output_eq_gen gen t⟩

lemma scored_subset_core (gen : FeedbackGenerator) :
    scored (Set.range (transcript gen).presentation)
      (transcript gen).presentation (transcript gen).output ⊆ core := by
  intro z hz
  rcases hz with ⟨⟨s, hs⟩, t, hyt, hnotobs⟩
  subst z
  rcases presentation_mem_core_or_ordinary gen s with hc | ho
  · exact hc
  · exfalso
    have hts : t < s := by
      by_contra h
      apply hnotobs
      exact ⟨s, by omega, rfl⟩
    have hsodd : Odd s := Nat.not_even_iff_odd.mp (by
      intro hseven
      rw [presentation_eq_nextX, nextX, dif_pos hseven] at ho
      exact ho ⟨s / 2, rfl⟩)
    obtain ⟨k, hk⟩ := hsodd
    have hsform : s = 2 * k + 1 := by omega
    subst s
    exact future_odd_ne_past_y gen hts hyt.symm

end Adversary

namespace Adversary

lemma fresh_lt_bound {t : ℕ} (h : Hist t) : fresh h < 6 * t + 5 := by
  have hm := fresh_mem_candidates h
  rw [candidates, Finset.mem_image] at hm
  obtain ⟨j, hj, heq⟩ := hm
  simp only [Finset.mem_range] at hj
  rw [← heq]
  omega

lemma odd_presentation_lt (gen : FeedbackGenerator) (m : ℕ) :
    (transcript gen).presentation (2 * m + 1) < 16 * (m + 1) := by
  rw [presentation_odd]
  have := fresh_lt_bound (histories gen (2 * m + 1))
  omega

noncomputable def target (gen : FeedbackGenerator) : Set ℕ :=
  Set.range (transcript gen).presentation

lemma target_infinite (gen : FeedbackGenerator) : (target gen).Infinite := by
  exact Set.infinite_range_of_injective (presentation_injective gen)

noncomputable def orderedTarget (gen : FeedbackGenerator) : OrderedLanguage := by
  classical
  exact {
    carrier := target gen
    enumeration := Nat.nth (fun z => z ∈ target gen)
    enumeration_injective := Nat.nth_injective (target_infinite gen)
    range_enumeration := Nat.range_nth_of_infinite (target_infinite gen)
  }

lemma orderedTarget_strictMono (gen : FeedbackGenerator) :
    InheritsAmbientOrder (orderedTarget gen) := by
  exact Nat.nth_strictMono (target_infinite gen)

noncomputable def targetCount (gen : FeedbackGenerator) (n : ℕ) : ℕ := by
  classical
  exact Nat.count (fun z => z ∈ target gen) n

lemma count_target_lower (gen : FeedbackGenerator) (n : ℕ) :
    n ≤ targetCount gen (16 * n) := by
  classical
  unfold targetCount
  rw [Nat.count_eq_card_filter_range]
  let source := Finset.range n
  let dest := (Finset.range (16 * n)).filter (fun z => z ∈ target gen)
  have hmap : Set.MapsTo (fun m => (transcript gen).presentation (2 * m + 1))
      (source : Set ℕ) (dest : Set ℕ) := by
    intro m hm
    simp only [source, Finset.mem_coe, Finset.mem_range] at hm
    simp only [dest, Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
    exact ⟨odd_presentation_lt gen m |>.trans_le (by omega),
      ⟨2 * m + 1, rfl⟩⟩
  have hinj : Set.InjOn (fun m => (transcript gen).presentation (2 * m + 1))
      (source : Set ℕ) := by
    intro a ha b hb hab
    have := presentation_injective gen hab
    omega
  have hcard := Finset.card_le_card_of_injOn _ hmap hinj
  simpa [source, dest] using hcard

lemma orderedTarget_enum_lt (gen : FeedbackGenerator) {i n : ℕ} (hin : i < n) :
    (orderedTarget gen).enumeration i < 16 * n := by
  classical
  apply Nat.nth_lt_of_lt_count
  change i < targetCount gen (16 * n)
  exact hin.trans_le (count_target_lower gen n)

lemma prefixCount_core_le (gen : FeedbackGenerator) (n : ℕ) :
    (orderedTarget gen).prefixCount core n ≤ Nat.log2 (16 * n) + 1 := by
  classical
  unfold GenLimit.KleinbergWei.OrderedLanguage.prefixCount
  let source := (Finset.range n).filter fun i => (orderedTarget gen).enumeration i ∈ core
  let dest := Finset.range (Nat.log2 (16 * n) + 1)
  let index : ℕ → ℕ := fun i => Nat.log2 ((orderedTarget gen).enumeration i)
  have hmap : Set.MapsTo index (source : Set ℕ) (dest : Set ℕ) := by
    intro i hi
    simp only [source, Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hi
    simp only [dest, Finset.mem_coe, Finset.mem_range, index]
    obtain ⟨k, hk⟩ := hi.2
    change 2 ^ k = (orderedTarget gen).enumeration i at hk
    have hlt : (orderedTarget gen).enumeration i < 16 * n := orderedTarget_enum_lt gen hi.1
    have hpos : 16 * n ≠ 0 := by omega
    have hkle : k ≤ Nat.log2 (16 * n) := by
      rw [Nat.le_log2 hpos]
      rw [hk]
      exact Nat.le_of_lt hlt
    rw [← hk, Nat.log2_two_pow]
    omega
  have hinj : Set.InjOn index (source : Set ℕ) := by
    intro i hi j hj hij
    simp only [source, Finset.mem_coe, Finset.mem_filter] at hi hj
    obtain ⟨ki, hki⟩ := hi.2
    obtain ⟨kj, hkj⟩ := hj.2
    change 2 ^ ki = (orderedTarget gen).enumeration i at hki
    change 2 ^ kj = (orderedTarget gen).enumeration j at hkj
    simp only [index, ← hki, ← hkj, Nat.log2_two_pow] at hij
    apply (orderedTarget gen).enumeration_injective
    rw [← hki, ← hkj, hij]
  have hcard := Finset.card_le_card_of_injOn index hmap hinj
  simpa [source, dest] using hcard

lemma log2_sixteen_mul (n : ℕ) (hn : n ≠ 0) :
    Nat.log2 (16 * n) = Nat.log2 n + 4 := by
  rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
  have hrewrite : 16 * n = (((n * 2) * 2) * 2) * 2 := by omega
  rw [hrewrite]
  rw [Nat.log_mul_base (by omega) (by positivity)]
  rw [Nat.log_mul_base (by omega) (by positivity)]
  rw [Nat.log_mul_base (by omega) (by positivity)]
  rw [Nat.log_mul_base (by omega) hn]

lemma tendsto_log_bound :
    Filter.Tendsto (fun n : ℕ => ((Nat.log2 (16 * n) + 1 : ℕ) : ℝ) / n)
      Filter.atTop (nhds 0) := by
  have hlog := GenLimit.tendsto_natLog2_div
  have hconst : Filter.Tendsto (fun n : ℕ => (5 : ℝ) / n) Filter.atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hsum : Filter.Tendsto (fun n : ℕ => (Nat.log2 n : ℝ) / n + 5 / n)
      Filter.atTop (nhds 0) := by
    simpa using hlog.add hconst
  have heq : (fun n : ℕ => (Nat.log2 n : ℝ) / n + 5 / n) =ᶠ[Filter.atTop]
      (fun n : ℕ => ((Nat.log2 (16 * n) + 1 : ℕ) : ℝ) / n) := by
    filter_upwards [Filter.eventually_ne_atTop 0] with n hn
    rw [log2_sixteen_mul n hn]
    push_cast
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    field_simp [hnR]
    ring
  exact Filter.Tendsto.congr' heq hsum

lemma upperDensity_core_zero (gen : FeedbackGenerator) :
    (orderedTarget gen).upperDensity core = 0 := by
  have hratio : ∀ n,
      (orderedTarget gen).prefixRatio core n ≤
        ((Nat.log2 (16 * n) + 1 : ℕ) : ℝ) / n := by
    intro n
    by_cases hn : n = 0
    · simp [hn]
    · simp only [GenLimit.KleinbergWei.OrderedLanguage.prefixRatio, hn, if_false]
      apply div_le_div_of_nonneg_right
      · exact_mod_cast prefixCount_core_le gen n
      · positivity
  have htendsto : Filter.Tendsto ((orderedTarget gen).prefixRatio core)
      Filter.atTop (nhds 0) := by
    apply squeeze_zero
      (fun n => (orderedTarget gen).prefixRatio_nonneg core n) hratio
      tendsto_log_bound
  exact htendsto.limsup_eq

lemma scored_density_zero (gen : FeedbackGenerator) :
    (orderedTarget gen).upperDensity
      (scored (target gen) (transcript gen).presentation (transcript gen).output) = 0 := by
  apply le_antisymm
  · calc
      (orderedTarget gen).upperDensity
          (scored (target gen) (transcript gen).presentation (transcript gen).output)
          ≤ (orderedTarget gen).upperDensity core :=
            (orderedTarget gen).upperDensity_mono (scored_subset_core gen)
      _ = 0 := upperDensity_core_zero gen
  · exact (orderedTarget gen).upperDensity_nonneg _

end Adversary

namespace Adversary

noncomputable def presenter (gen : FeedbackGenerator) : CausalPresenter where
  next t xp qp ap yp := nextX ⟨xp, qp, ap, yp⟩

lemma presented_by (gen : FeedbackGenerator) :
    PresentedBy (presenter gen) (transcript gen) := by
  intro t
  rw [presentation_eq_nextX]
  unfold presenter
  have hh :
      Hist.mk
        (fun i => (transcript gen).presentation i)
        (fun i => (transcript gen).query i)
        (fun i => (transcript gen).answer i)
        (fun i => (transcript gen).output i) =
      histories gen t := by
    have hx := transcript_x_hist gen t
    have hq := transcript_q_hist gen t
    have ha := transcript_a_hist gen t
    have hy := transcript_y_hist gen t
    cases hhist : histories gen t with
    | mk x q a y =>
        rw [hhist] at hx hq ha hy
        simp only [Hist.mk.injEq]
        exact ⟨hx, hq, ha, hy⟩
  exact congrArg nextX hh.symm

lemma faithful_witness (gen : FeedbackGenerator) :
    FaithfulNegativeWitness gen (target gen) (presenter gen)
      (transcript gen) (orderedTarget gen) := by
  refine ⟨rfl, orderedTarget_strictMono gen, presented_by gen,
    follows_protocol gen, ?_, presentation_injective gen, ?_, scored_density_zero gen⟩
  · exact target_clean gen
  · exact target_complete gen

lemma negative_claim : NegativeClaim := by
  intro gen hvalid
  refine ⟨target gen, ?_, presenter gen, transcript gen, orderedTarget gen, faithful_witness gen⟩
  exact target_mem_class gen

end Adversary

theorem stage3_result : Stage3S2B.MainClaim := by
  exact ⟨targetClass_not_countable, uniform_generation, Adversary.negative_claim⟩
