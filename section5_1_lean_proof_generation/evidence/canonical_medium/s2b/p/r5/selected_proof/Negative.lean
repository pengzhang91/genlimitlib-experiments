import Stage3Model
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.Log
import Mathlib.Analysis.SpecialFunctions.Log.Base

open Set Filter

namespace Stage3Work
open Stage3S2B

noncomputable section

private def extend {α : Type} {t : ℕ} (f : Fin t → α) (x : α) : Fin (t+1) → α :=
  Fin.lastCases x f

private structure Hist (t : ℕ) where
  p : Fin t → ℕ
  q : Fin t → Option ℕ
  a : Fin t → Option Bool
  y : Fin t → ℕ
  admitted : Finset ℕ
  rejected : Finset ℕ

private def emptyHist : Hist 0 where
  p := Fin.elim0
  q := Fin.elim0
  a := Fin.elim0
  y := Fin.elim0
  admitted := ∅
  rejected := ∅

private theorem ordinary_infinite : ordinary.Infinite := by
  let f : ℕ → ℕ := fun n => 2*n+3
  have hf : Function.Injective f := by intro a b h; simp [f] at h; omega
  have hr : Set.range f ⊆ ordinary := by
    rintro z ⟨n, rfl⟩
    rintro ⟨k, hk⟩
    by_cases h0 : k = 0
    · subst k; dsimp [f] at hk; omega
    · have he : Even (2^k) := Nat.even_pow.mpr ⟨by simp, h0⟩
      have ho : Odd (2*n+3) := ⟨n+1, by omega⟩
      have hne : ¬ Even (2*n+3) := Nat.not_even_iff_odd.mpr ho
      dsimp [f] at hk
      exact hne (hk ▸ he)
  exact (Set.infinite_range_of_injective hf).mono hr

private noncomputable def freshOrdinary (I R : Finset ℕ) : ℕ := by
  classical
  exact Nat.find (ordinary_infinite.exists_not_mem_finset (I ∪ R))

private theorem freshOrdinary_spec (I R : Finset ℕ) :
    freshOrdinary I R ∈ ordinary ∧ freshOrdinary I R ∉ I ∪ R := by
  classical
  exact Nat.find_spec (ordinary_infinite.exists_not_mem_finset (I ∪ R))


private noncomputable def addReject (I R : Finset ℕ) (z : ℕ) : Finset ℕ := by
  classical
  exact if z ∈ core ∨ z ∈ I ∨ z ∈ R then R else insert z R


private noncomputable def queryReject (I R : Finset ℕ) (q : Option ℕ) : Finset ℕ :=
  q.elim R (addReject I R)

private def step (gen : FeedbackGenerator) {t : ℕ} (h : Hist t) : Hist (t+1) := by
  classical
  let odd := t % 2 = 1
  let x := if odd then freshOrdinary h.admitted h.rejected else 2^(t/2)
  let I' := if odd then insert x h.admitted else h.admitted
  let pp := extend h.p x
  let query := gen.query t pp h.a
  let answer := query.map fun z => membershipAnswer (core ∪ (I' : Set ℕ)) z
  let Rq := queryReject I' h.rejected query
  let aa := extend h.a answer
  let out := gen.output t pp aa
  let R' := addReject I' Rq out
  exact {
    p := pp, q := extend h.q query, a := aa, y := extend h.y out,
    admitted := I', rejected := R' }

private def build (gen : FeedbackGenerator) : (t : ℕ) → Hist t
  | 0 => emptyHist
  | t+1 => step gen (build gen t)

private def tr (gen : FeedbackGenerator) : Transcript where
  presentation t := (build gen (t+1)).p (Fin.last t)
  query t := (build gen (t+1)).q (Fin.last t)
  answer t := (build gen (t+1)).a (Fin.last t)
  output t := (build gen (t+1)).y (Fin.last t)

private theorem build_succ_p (gen : FeedbackGenerator) (t : ℕ) (i : Fin t) :
    (build gen (t+1)).p i.castSucc = (build gen t).p i := by
  simp [build, step, extend]

private theorem build_succ_q (gen : FeedbackGenerator) (t : ℕ) (i : Fin t) :
    (build gen (t+1)).q i.castSucc = (build gen t).q i := by
  simp [build, step, extend]

private theorem build_succ_a (gen : FeedbackGenerator) (t : ℕ) (i : Fin t) :
    (build gen (t+1)).a i.castSucc = (build gen t).a i := by
  simp [build, step, extend]

private theorem build_succ_y (gen : FeedbackGenerator) (t : ℕ) (i : Fin t) :
    (build gen (t+1)).y i.castSucc = (build gen t).y i := by
  simp [build, step, extend]

private theorem tr_history_p (gen : FeedbackGenerator) (t : ℕ) :
    (fun i : Fin t => (tr gen).presentation i) = (build gen t).p := by
  funext i
  induction t with
  | zero => exact Fin.elim0 i
  | succ t ih =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [tr, build, step, extend]
      · rw [build_succ_p]
        exact ih j

private theorem tr_history_q (gen : FeedbackGenerator) (t : ℕ) :
    (fun i : Fin t => (tr gen).query i) = (build gen t).q := by
  funext i
  induction t with
  | zero => exact Fin.elim0 i
  | succ t ih =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [tr, build, step, extend]
      · rw [build_succ_q]
        exact ih j

private theorem tr_history_a (gen : FeedbackGenerator) (t : ℕ) :
    (fun i : Fin t => (tr gen).answer i) = (build gen t).a := by
  funext i
  induction t with
  | zero => exact Fin.elim0 i
  | succ t ih =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [tr, build, step, extend]
      · rw [build_succ_a]
        exact ih j

private theorem tr_history_y (gen : FeedbackGenerator) (t : ℕ) :
    (fun i : Fin t => (tr gen).output i) = (build gen t).y := by
  funext i
  induction t with
  | zero => exact Fin.elim0 i
  | succ t ih =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [tr, build, step, extend]
      · rw [build_succ_y]
        exact ih j

end
end Stage3Work

namespace Stage3Work
open Stage3S2B
noncomputable section

private def I (gen : FeedbackGenerator) (t : ℕ) := (build gen t).admitted
private def R (gen : FeedbackGenerator) (t : ℕ) := (build gen t).rejected
private def limitA (gen : FeedbackGenerator) : Set ℕ := {z | ∃ t, z ∈ I gen t}
private def target (gen : FeedbackGenerator) : Set ℕ := core ∪ limitA gen

private theorem addReject_subset (I R : Finset ℕ) (z : ℕ) : R ⊆ addReject I R z := by
  classical
  by_cases h : z ∈ core ∨ z ∈ I ∨ z ∈ R <;> simp [addReject, h]

private theorem queryReject_subset (I R : Finset ℕ) (q : Option ℕ) :
    R ⊆ queryReject I R q := by
  cases q with
  | none => exact fun _ h => h
  | some z => exact addReject_subset I R z

private theorem addReject_ordinary (I R : Finset ℕ) (z : ℕ)
    (hR : ∀ w ∈ R, w ∈ ordinary) : ∀ w ∈ addReject I R z, w ∈ ordinary := by
  classical
  by_cases h : z ∈ core ∨ z ∈ I ∨ z ∈ R
  · simpa [addReject, h] using hR
  · intro w hw
    simp [addReject, h] at hw
    rcases hw with rfl | hw
    · intro hc
      exact h (Or.inl hc)
    · exact hR w hw

private theorem queryReject_ordinary (I R : Finset ℕ) (q : Option ℕ)
    (hR : ∀ w ∈ R, w ∈ ordinary) : ∀ w ∈ queryReject I R q, w ∈ ordinary := by
  cases q with
  | none => exact hR
  | some z => exact addReject_ordinary I R z hR

private theorem addReject_disjoint (I R : Finset ℕ) (z : ℕ) (hIR : Disjoint I R) :
    Disjoint I (addReject I R z) := by
  classical
  rw [Finset.disjoint_left] at hIR ⊢
  by_cases h : z ∈ core ∨ z ∈ I ∨ z ∈ R
  · simpa [addReject, h] using hIR
  · intro a ha
    simp only [addReject, h, if_false, Finset.mem_insert, not_or]
    exact ⟨fun haz => h (Or.inr (Or.inl (haz ▸ ha))), hIR ha⟩

private theorem queryReject_disjoint (I R : Finset ℕ) (q : Option ℕ) (hIR : Disjoint I R) :
    Disjoint I (queryReject I R q) := by
  cases q with
  | none => exact hIR
  | some z => exact addReject_disjoint I R z hIR

private theorem I_step_subset (gen : FeedbackGenerator) (t : ℕ) : I gen t ⊆ I gen (t+1) := by
  classical
  by_cases h : t % 2 = 1 <;> simp [I, build, step, h]

private theorem R_step_subset (gen : FeedbackGenerator) (t : ℕ) : R gen t ⊆ R gen (t+1) := by
  classical
  simp only [R, build, step]
  exact fun z hz => addReject_subset _ _ _ (queryReject_subset _ _ _ hz)

private theorem I_mono (gen : FeedbackGenerator) {s t : ℕ} (hst : s ≤ t) : I gen s ⊆ I gen t := by
  induction t, hst using Nat.le_induction with
  | base => exact fun _ h => h
  | succ t hst ih => exact fun z hz => I_step_subset gen t (ih hz)

private theorem R_mono (gen : FeedbackGenerator) {s t : ℕ} (hst : s ≤ t) : R gen s ⊆ R gen t := by
  induction t, hst using Nat.le_induction with
  | base => exact fun _ h => h
  | succ t hst ih => exact fun z hz => R_step_subset gen t (ih hz)

private theorem admitted_ordinary (gen : FeedbackGenerator) (t : ℕ) :
    ∀ z ∈ I gen t, z ∈ ordinary := by
  induction t with
  | zero => simp [I, build, emptyHist]
  | succ t ih =>
      classical
      by_cases h : t % 2 = 1
      · simp only [I, build, step, h, if_true]
        intro z hz
        simp only [Finset.mem_insert] at hz
        rcases hz with rfl | hz
        · exact (freshOrdinary_spec _ _).1
        · exact ih z hz
      · simpa [I, build, step, h] using ih

private theorem rejected_ordinary (gen : FeedbackGenerator) (t : ℕ) :
    ∀ z ∈ R gen t, z ∈ ordinary := by
  induction t with
  | zero => simp [R, build, emptyHist]
  | succ t ih =>
      classical
      simp only [R, build, step]
      exact addReject_ordinary _ _ _ (queryReject_ordinary _ _ _ ih)

private theorem disjoint_IR (gen : FeedbackGenerator) (t : ℕ) :
    Disjoint (I gen t) (R gen t) := by
  induction t with
  | zero => simp [I, R, build, emptyHist]
  | succ t ih =>
      classical
      simp only [I, R, build, step]
      by_cases h : t % 2 = 1
      · simp only [h, if_true]
        have hf := (freshOrdinary_spec (build gen t).admitted (build gen t).rejected).2
        have hbase : Disjoint (insert (freshOrdinary (build gen t).admitted (build gen t).rejected)
            (build gen t).admitted) (build gen t).rejected := by
          rw [Finset.disjoint_left] at ih ⊢
          simp only [Finset.mem_insert, forall_eq_or_imp]
          exact ⟨(fun hr => hf (Finset.mem_union_right _ hr)), ih⟩
        exact addReject_disjoint _ _ _ (queryReject_disjoint _ _ _ hbase)
      · simp only [h, if_false]
        exact addReject_disjoint _ _ _ (queryReject_disjoint _ _ _ ih)

private theorem rejected_never_admitted (gen : FeedbackGenerator) {s t : ℕ} {z : ℕ}
    (hz : z ∈ R gen s) : z ∉ I gen t := by
  intro hi
  let u := max s t
  have hr : z ∈ R gen u := R_mono gen (Nat.le_max_left _ _) hz
  have ha : z ∈ I gen u := I_mono gen (Nat.le_max_right _ _) hi
  exact (Finset.disjoint_left.mp (disjoint_IR gen u)) ha hr

private theorem target_mem_iff_stage (gen : FeedbackGenerator) (t : ℕ) (z : ℕ)
    (decided : z ∈ I gen t ∨ z ∈ R gen t) :
    z ∈ target gen ↔ z ∈ core ∨ z ∈ I gen t := by
  constructor
  · rintro (hc | ⟨u, hu⟩)
    · exact Or.inl hc
    · right
      rcases decided with hi | hr
      · exact hi
      · exact False.elim (rejected_never_admitted gen hr hu)
  · rintro (hc | hi)
    · exact Or.inl hc
    · exact Or.inr ⟨t, hi⟩

end
end Stage3Work

namespace Stage3Work
open Stage3S2B
noncomputable section

private theorem target_in_class (gen : FeedbackGenerator) : target gen ∈ targetClass := by
  refine ⟨limitA gen, ?_, rfl⟩
  rintro z ⟨t, ht⟩
  exact admitted_ordinary gen t z ht

private theorem I_succ_eq (gen : FeedbackGenerator) (t : ℕ) :
    I gen (t+1) = if t % 2 = 1 then insert (freshOrdinary (I gen t) (R gen t)) (I gen t) else I gen t := by
  classical
  by_cases h : t % 2 = 1 <;> simp [I, R, build, step, h]

private theorem tr_query_eq (gen : FeedbackGenerator) (t : ℕ) :
    (tr gen).query t = gen.query t (build gen (t+1)).p (build gen t).a := by
  simp [tr, build, step, extend]

private theorem tr_answer_eq (gen : FeedbackGenerator) (t : ℕ) :
    (tr gen).answer t = (gen.query t (build gen (t+1)).p (build gen t).a).map
      (fun z => membershipAnswer (core ∪ (I gen (t+1) : Set ℕ)) z) := by
  classical
  by_cases h : t % 2 = 1 <;> simp [tr, build, step, extend, I, h]

private theorem tr_output_eq (gen : FeedbackGenerator) (t : ℕ) :
    (tr gen).output t = gen.output t (build gen (t+1)).p (build gen (t+1)).a := by
  simp [tr, build, step, extend]

private theorem query_decided (gen : FeedbackGenerator) (t z : ℕ)
    (hnc : z ∉ core) (hq : (tr gen).query t = some z) :
    z ∈ I gen (t+1) ∨ z ∈ R gen (t+1) := by
  classical
  have hq' : gen.query t (build gen (t+1)).p (build gen t).a = some z := by
    rw [← tr_query_eq]
    exact hq
  by_cases hi : z ∈ I gen (t+1)
  · exact Or.inl hi
  · right
    simp only [R, build, step]
    apply addReject_subset
    simp only [I, build, step] at hi
    have hqraw : gen.query t
        (extend (build gen t).p
          (if t % 2 = 1 then freshOrdinary (build gen t).admitted (build gen t).rejected else 2^(t/2)))
        (build gen t).a = some z := by
      simpa [build, step] using hq'
    rw [hqraw]
    simp only [queryReject, Option.elim, Option.rec]
    simp only [addReject, hnc, hi, false_or]
    by_cases hr : z ∈ (build gen t).rejected <;> simp [hr]

private theorem membershipAnswer_congr {K L : Set ℕ} {z : ℕ} (h : z ∈ K ↔ z ∈ L) :
    membershipAnswer K z = membershipAnswer L z := by
  classical
  simp only [membershipAnswer]
  congr 1
  exact propext h

private theorem queried_answer_truthful (gen : FeedbackGenerator) (t z : ℕ)
    (hq : (tr gen).query t = some z) :
    membershipAnswer (target gen) z = membershipAnswer (core ∪ (I gen (t+1) : Set ℕ)) z := by
  by_cases hc : z ∈ core
  · apply membershipAnswer_congr
    constructor <;> intro
    · exact Or.inl hc
    · exact Or.inl hc
  · apply membershipAnswer_congr
    exact target_mem_iff_stage gen (t+1) z (query_decided gen t z hc hq)

private theorem follows_protocol (gen : FeedbackGenerator) :
    FollowsProtocol gen (target gen) (tr gen) := by
  intro t
  constructor
  · rw [tr_query_eq, tr_history_p, tr_history_a]
  constructor
  · rw [tr_answer_eq, tr_query_eq]
    cases hq : gen.query t (build gen (t+1)).p (build gen t).a with
    | none => rfl
    | some z =>
        simp only [Option.map_some, Option.some.injEq]
        symm
        apply queried_answer_truthful gen t z
        rw [tr_query_eq, hq]
  · rw [tr_output_eq, tr_history_p, tr_history_a]

end
end Stage3Work

namespace Stage3Work
open Stage3S2B
noncomputable section

private theorem presentation_eq (gen : FeedbackGenerator) (t : ℕ) :
    (tr gen).presentation t = if t % 2 = 1 then freshOrdinary (I gen t) (R gen t) else 2^(t/2) := by
  classical
  simp [tr, build, step, extend, I, R]

private theorem odd_presented_admitted (gen : FeedbackGenerator) (t : ℕ) (h : t % 2 = 1) :
    (tr gen).presentation t ∈ I gen (t+1) := by
  rw [presentation_eq, I_succ_eq]
  simp [h]

private theorem odd_presented_ordinary (gen : FeedbackGenerator) (t : ℕ) (h : t % 2 = 1) :
    (tr gen).presentation t ∈ ordinary := by
  rw [presentation_eq]
  simp only [h, if_true]
  exact (freshOrdinary_spec _ _).1

private theorem even_presented_core (gen : FeedbackGenerator) (t : ℕ) (h : t % 2 ≠ 1) :
    (tr gen).presentation t ∈ core := by
  rw [presentation_eq]
  simp only [h, if_false]
  exact ⟨t/2, rfl⟩

private theorem clean_presentation (gen : FeedbackGenerator) : Clean (tr gen).presentation (target gen) := by
  intro t
  by_cases h : t % 2 = 1
  · exact Or.inr ⟨t+1, odd_presented_admitted gen t h⟩
  · exact Or.inl (even_presented_core gen t h)

private theorem admitted_was_presented (gen : FeedbackGenerator) (t : ℕ) :
    ∀ z ∈ I gen t, ∃ s, s < t ∧ (tr gen).presentation s = z := by
  induction t with
  | zero => simp [I, build, emptyHist]
  | succ t ih =>
      classical
      intro z hz
      rw [I_succ_eq] at hz
      by_cases h : t % 2 = 1
      · simp only [h, if_true, Finset.mem_insert] at hz
        rcases hz with rfl | hz
        · exact ⟨t, Nat.lt_succ_self t, by simp [presentation_eq, h, I, R]⟩
        · rcases ih z hz with ⟨s, hs, heq⟩
          exact ⟨s, hs.trans (Nat.lt_succ_self t), heq⟩
      · simp only [h, if_false] at hz
        rcases ih z hz with ⟨s, hs, heq⟩
        exact ⟨s, hs.trans (Nat.lt_succ_self t), heq⟩

private theorem complete_presentation (gen : FeedbackGenerator) :
    Complete (tr gen).presentation (target gen) := by
  intro z hz
  rcases hz with ⟨k, rfl⟩ | ⟨t, ht⟩
  · refine ⟨2*k, ?_⟩
    rw [presentation_eq]
    simp
  · rcases admitted_was_presented gen t z ht with ⟨s, hs, heq⟩
    exact ⟨s, heq⟩

private theorem presentation_pairwise (gen : FeedbackGenerator) {s t : ℕ} (hst : s < t) :
    (tr gen).presentation s ≠ (tr gen).presentation t := by
  by_cases ht : t % 2 = 1
  · have htord := odd_presented_ordinary gen t ht
    by_cases hs : s % 2 = 1
    · have hsi : (tr gen).presentation s ∈ I gen (s+1) := odd_presented_admitted gen s hs
      have hle : s+1 ≤ t := hst
      have hit : (tr gen).presentation s ∈ I gen t := I_mono gen hle hsi
      rw [presentation_eq gen t]
      simp only [ht, if_true]
      intro heq
      have hf := (freshOrdinary_spec (I gen t) (R gen t)).2
      exact hf (Finset.mem_union_left _ (heq ▸ hit))
    · have hscore := even_presented_core gen s hs
      intro heq
      exact htord (heq ▸ hscore)
  · have htcore := even_presented_core gen t ht
    by_cases hs : s % 2 = 1
    · have hsord := odd_presented_ordinary gen s hs
      intro heq
      exact hsord (heq ▸ htcore)
    · rw [presentation_eq gen s, presentation_eq gen t]
      simp only [hs, ht, if_false]
      intro heq
      have he : s / 2 = t / 2 := Nat.pow_right_injective (by decide) heq
      have hsmod : s % 2 = 0 := by omega
      have htmod : t % 2 = 0 := by omega
      have hsrepr := (Nat.mod_add_div s 2).symm
      have htrepr := (Nat.mod_add_div t 2).symm
      omega

private theorem injective_presentation (gen : FeedbackGenerator) :
    Function.Injective (tr gen).presentation := by
  intro s t h
  rcases lt_trichotomy s t with hst | rfl | hts
  · exact False.elim (presentation_pairwise gen hst h)
  · rfl
  · exact False.elim (presentation_pairwise gen hts h.symm)

private def presenter (gen : FeedbackGenerator) : CausalPresenter where
  next t _ _ _ _ := (tr gen).presentation t

private theorem presented_by (gen : FeedbackGenerator) : PresentedBy (presenter gen) (tr gen) := by
  intro t
  rfl

end
end Stage3Work

namespace Stage3Work
open Stage3S2B
noncomputable section

private theorem mem_addReject_self (I R : Finset ℕ) (z : ℕ)
    (hnc : z ∉ core) (hni : z ∉ I) : z ∈ addReject I R z := by
  classical
  by_cases hr : z ∈ R <;> simp [addReject, hnc, hni, hr]

private theorem output_rejected (gen : FeedbackGenerator) (t z : ℕ)
    (hnc : z ∉ core) (hni : z ∉ I gen (t+1)) (hy : (tr gen).output t = z) :
    z ∈ R gen (t+1) := by
  classical
  rw [tr_output_eq] at hy
  simp only [build, step] at hy
  simp only [R, build, step]
  rw [hy]
  exact mem_addReject_self _ _ _ hnc hni

private theorem scored_subset_core (gen : FeedbackGenerator) :
    scored (target gen) (tr gen).presentation (tr gen).output ⊆ core := by
  intro z hz
  rcases hz with ⟨hzK, t, hyt, hnot⟩
  by_contra hnc
  rcases hzK with hc | ⟨u, hu⟩
  · exact hnc hc
  · have hni : z ∉ I gen (t+1) := by
      intro hi
      rcases admitted_was_presented gen (t+1) z hi with ⟨s, hs, heq⟩
      apply hnot
      exact ⟨s, by omega, heq⟩
    have hr : z ∈ R gen (t+1) := output_rejected gen t z hnc hni hyt
    exact rejected_never_admitted gen hr hu

private theorem target_infinite (gen : FeedbackGenerator) : (target gen).Infinite := by
  have hr : (Set.range (fun n : ℕ => 2^n)).Infinite :=
    Set.infinite_range_of_injective (Nat.pow_right_injective (show 2 ≤ (2:ℕ) by decide))
  apply hr.mono
  intro z hz
  exact Or.inl hz

private def orderedTarget (gen : FeedbackGenerator) : OrderedLanguage where
  carrier := target gen
  enumeration := Nat.nth (fun z => z ∈ target gen)
  enumeration_injective := Nat.nth_injective (target_infinite gen)
  range_enumeration := Nat.range_nth_of_infinite (target_infinite gen)

private theorem orderedTarget_inherits (gen : FeedbackGenerator) :
    InheritsAmbientOrder (orderedTarget gen) :=
  Nat.nth_strictMono (target_infinite gen)

end
end Stage3Work

namespace Stage3Work
open Stage3S2B
noncomputable section

private def ordCode (n : ℕ) := 2*n+3
private theorem ordCode_injective : Function.Injective ordCode := by
  intro a b h
  simp [ordCode] at h
  omega
private theorem ordCode_ordinary (n : ℕ) : ordCode n ∈ ordinary := by
  rintro ⟨k, hk⟩
  by_cases h0 : k = 0
  · subst k
    simp [ordCode] at hk
  · have he : Even (2^k) := Nat.even_pow.mpr ⟨by simp, h0⟩
    have ho : Odd (ordCode n) := ⟨n+1, by simp [ordCode]; omega⟩
    have hne : ¬ Even (ordCode n) := Nat.not_even_iff_odd.mpr ho
    exact hne (hk ▸ he)

private theorem exists_code_not_mem (S : Finset ℕ) :
    ∃ n ≤ S.card, ordCode n ∉ S := by
  by_contra h
  push_neg at h
  have hsub : (Finset.range (S.card+1)).image ordCode ⊆ S := by
    intro z hz
    simp only [Finset.mem_image, Finset.mem_range] at hz
    rcases hz with ⟨n, hn, rfl⟩
    exact h n (by omega)
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ ordCode_injective, Finset.card_range] at hc
  omega

private theorem fresh_bound (I R : Finset ℕ) :
    freshOrdinary I R ≤ 2 * (I ∪ R).card + 3 := by
  classical
  rcases exists_code_not_mem (I ∪ R) with ⟨n, hn, hmem⟩
  calc
    freshOrdinary I R ≤ ordCode n := by
      apply Nat.find_min' (ordinary_infinite.exists_not_mem_finset (I ∪ R))
      exact ⟨ordCode_ordinary n, hmem⟩
    _ ≤ 2 * (I ∪ R).card + 3 := by
      simp [ordCode]
      omega

private theorem card_addReject_le (I R : Finset ℕ) (z : ℕ) :
    (addReject I R z).card ≤ R.card + 1 := by
  classical
  by_cases h : z ∈ core ∨ z ∈ I ∨ z ∈ R
  · simp [addReject, h]
  · simpa [addReject, h] using Finset.card_insert_le z R

private theorem card_queryReject_le (I R : Finset ℕ) (q : Option ℕ) :
    (queryReject I R q).card ≤ R.card + 1 := by
  cases q with
  | none => simp [queryReject]
  | some z => exact card_addReject_le I R z

private theorem card_I_le (gen : FeedbackGenerator) (t : ℕ) : (I gen t).card ≤ t := by
  induction t with
  | zero => simp [I, build, emptyHist]
  | succ t ih =>
      classical
      rw [I_succ_eq]
      by_cases h : t % 2 = 1
      · simp only [h, if_true]
        calc
          (insert (freshOrdinary (I gen t) (R gen t)) (I gen t)).card ≤ (I gen t).card + 1 := Finset.card_insert_le _ _
          _ ≤ t+1 := by omega
      · simpa [h] using Nat.le_trans ih (Nat.le_succ t)

private theorem card_R_le (gen : FeedbackGenerator) (t : ℕ) : (R gen t).card ≤ 2*t := by
  induction t with
  | zero => simp [R, build, emptyHist]
  | succ t ih =>
      classical
      simp only [R, build, step]
      calc
        (addReject _ (queryReject _ (build gen t).rejected _) _).card ≤
            (queryReject _ (build gen t).rejected _).card + 1 := card_addReject_le _ _ _
        _ ≤ (build gen t).rejected.card + 2 := by
          have := card_queryReject_le
            (if t % 2 = 1 then insert (if t % 2 = 1 then freshOrdinary (build gen t).admitted
              (build gen t).rejected else 2^(t/2)) (build gen t).admitted else (build gen t).admitted)
            (build gen t).rejected
            (gen.query t (extend (build gen t).p
              (if t % 2 = 1 then freshOrdinary (build gen t).admitted (build gen t).rejected else 2^(t/2)))
              (build gen t).a)
          omega
        _ ≤ 2*(t+1) := by
          change (R gen t).card + 2 ≤ 2*(t+1)
          omega

private theorem odd_presentation_bound (gen : FeedbackGenerator) (r : ℕ) :
    (tr gen).presentation (2*r+1) ≤ 12*r+9 := by
  have hodd : (2*r+1) % 2 = 1 := by omega
  rw [presentation_eq]
  simp only [hodd, if_true]
  calc
    freshOrdinary (I gen (2*r+1)) (R gen (2*r+1)) ≤
        2 * ((I gen (2*r+1)) ∪ (R gen (2*r+1))).card + 3 := fresh_bound _ _
    _ ≤ 12*r+9 := by
      have hi := card_I_le gen (2*r+1)
      have hr := card_R_le gen (2*r+1)
      have hu := Finset.card_union_le (I gen (2*r+1)) (R gen (2*r+1))
      omega

private theorem nth_target_bound (gen : FeedbackGenerator) (n : ℕ) :
    Nat.nth (fun z => z ∈ target gen) n ≤ 12*n+9 := by
  classical
  let vals : Finset ℕ := (Finset.range (n+1)).image (fun r => (tr gen).presentation (2*r+1))
  have hfuninj : Function.Injective (fun r => (tr gen).presentation (2*r+1)) := by
    intro a b hab
    have hinj := injective_presentation gen hab
    omega
  have hcard : vals.card = n+1 := by
    dsimp [vals]
    rw [Finset.card_image_of_injective _ hfuninj, Finset.card_range]
  have hsub : vals ⊆ (Finset.range (12*n+10)).filter (fun z => z ∈ target gen) := by
    intro z hz
    simp only [vals, Finset.mem_image, Finset.mem_range] at hz
    rcases hz with ⟨r, hr, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · have hb := odd_presentation_bound gen r
      omega
    · exact clean_presentation gen (2*r+1)
  have hc : n+1 ≤ Nat.count (fun z => z ∈ target gen) (12*n+10) := by
    rw [Nat.count_eq_card_filter_range]
    rw [← hcard]
    exact Finset.card_le_card hsub
  have hlt : n < Nat.count (fun z => z ∈ target gen) (12*n+10) := by omega
  have := Nat.nth_lt_of_lt_count hlt
  omega

end
end Stage3Work

namespace Stage3Work
open Stage3S2B
open GenLimit.KleinbergWei.OrderedLanguage
noncomputable section

private theorem prefixCount_core_le (gen : FeedbackGenerator) (n : ℕ) :
    (orderedTarget gen).prefixCount core n ≤ Nat.log 2 (12*n+9) + 1 := by
  classical
  change ((Finset.range n).filter fun i => (orderedTarget gen).enumeration i ∈ core).card ≤ _
  rw [← Finset.card_range (Nat.log 2 (12*n+9) + 1)]
  apply Finset.card_le_card_of_injOn (fun i => Nat.log 2 ((orderedTarget gen).enumeration i))
  · intro i hi
    change i ∈ (Finset.range n).filter (fun i => (orderedTarget gen).enumeration i ∈ core) at hi
    simp only [Finset.mem_filter, Finset.mem_range] at hi
    rcases hi.2 with ⟨k, hk⟩
    change 2 ^ k = (orderedTarget gen).enumeration i at hk
    have hlt : Nat.log 2 ((orderedTarget gen).enumeration i) < Nat.log 2 (12*n+9) + 1 := by
      rw [← hk, Nat.log_pow (by decide)]
      apply Nat.lt_succ_of_le
      apply Nat.le_log_of_pow_le (by decide)
      calc
        2 ^ k = (orderedTarget gen).enumeration i := hk
        _ ≤ Nat.nth (fun z => z ∈ target gen) n := by
          apply (orderedTarget_inherits gen).monotone
          exact Nat.le_of_lt hi.1
        _ ≤ 12*n+9 := nth_target_bound gen n
    simpa using hlt
  · intro i hi j hj heq
    change i ∈ (Finset.range n).filter (fun i => (orderedTarget gen).enumeration i ∈ core) at hi
    change j ∈ (Finset.range n).filter (fun i => (orderedTarget gen).enumeration i ∈ core) at hj
    simp only [Finset.mem_filter, Finset.mem_range] at hi hj
    rcases hi.2 with ⟨ki, hki⟩
    rcases hj.2 with ⟨kj, hkj⟩
    change 2 ^ ki = (orderedTarget gen).enumeration i at hki
    change 2 ^ kj = (orderedTarget gen).enumeration j at hkj
    dsimp only at heq
    rw [← hki, Nat.log_pow (by decide), ← hkj, Nat.log_pow (by decide)] at heq
    apply (orderedTarget gen).enumeration_injective
    exact hki.symm.trans ((congrArg (fun k => 2 ^ k) heq).trans hkj)

private theorem prefixCount_mono {K : OrderedLanguage} {A B : Language}
    (hAB : A ⊆ B) (n : ℕ) : K.prefixCount A n ≤ K.prefixCount B n := by
  classical
  apply Finset.card_le_card
  intro i hi
  simp only [GenLimit.KleinbergWei.OrderedLanguage.prefixCount, Finset.mem_filter,
    Finset.mem_range] at hi ⊢
  exact ⟨hi.1, hAB hi.2⟩

end
end Stage3Work

namespace Stage3Work
open Stage3S2B
open GenLimit.KleinbergWei.OrderedLanguage
noncomputable section

private theorem log_bound_tendsto :
    Tendsto (fun n : ℕ => (Real.logb 2 (12*n+9) + 1) / (n:ℝ)) atTop (nhds 0) := by
  have hmul : Tendsto (fun n : ℕ => (12 : ℝ) * n) atTop atTop :=
    Tendsto.const_mul_atTop (by norm_num) tendsto_natCast_atTop_atTop
  have harg : Tendsto (fun n : ℕ => (12 : ℝ) * n + 9) atTop atTop :=
    tendsto_atTop_add_const_right atTop 9 hmul
  have hlog :=
    (Real.tendsto_pow_logb_div_mul_add_atTop (b := (2:ℝ)) (1/12) (-3/4) 1
      (by norm_num)).comp harg
  have hlog' : Tendsto (fun n : ℕ => Real.logb 2 (12*n+9) / (n:ℝ)) atTop (nhds 0) := by
    convert hlog using 1
    funext n
    simp only [pow_one]
    congr 2 <;> norm_num <;> ring
  have hadd := hlog'.add (tendsto_const_div_atTop_nhds_zero_nat 1)
  rw [zero_add] at hadd
  convert hadd using 1
  funext n
  rw [add_div]

private theorem scored_prefixRatio_tendsto (gen : FeedbackGenerator) :
    Tendsto ((orderedTarget gen).prefixRatio
      (scored (target gen) (tr gen).presentation (tr gen).output)) atTop (nhds 0) := by
  refine squeeze_zero (g := fun n : ℕ => (Real.logb 2 (12*n+9) + 1) / (n:ℝ)) ?_ ?_ log_bound_tendsto
  · intro n
    simp only [prefixRatio]
    split_ifs
    · exact le_rfl
    · positivity
  · intro n
    by_cases hn : n = 0
    · simp [prefixRatio, hn]
    · rw [prefixRatio, if_neg hn]
      have hcountNat :
          (orderedTarget gen).prefixCount
              (scored (target gen) (tr gen).presentation (tr gen).output) n ≤
            Nat.log 2 (12*n+9) + 1 :=
        (prefixCount_mono (scored_subset_core gen) n).trans (prefixCount_core_le gen n)
      have hcountReal :
          ((orderedTarget gen).prefixCount
              (scored (target gen) (tr gen).presentation (tr gen).output) n : ℝ) ≤
            (Nat.log 2 (12*n+9) + 1 : ℕ) := by
        exact_mod_cast hcountNat
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
      calc
        ((orderedTarget gen).prefixCount
            (scored (target gen) (tr gen).presentation (tr gen).output) n : ℝ) ≤
            (Nat.log 2 (12*n+9) + 1 : ℕ) := hcountReal
        _ = (Nat.log 2 (12*n+9) : ℝ) + 1 := by norm_num
        _ ≤ Real.logb 2 (12*n+9) + 1 := by
          gcongr
          convert Real.natLog_le_logb (12*n+9) 2 using 1 <;> norm_num

private theorem scored_density_zero (gen : FeedbackGenerator) :
    (orderedTarget gen).upperDensity
      (scored (target gen) (tr gen).presentation (tr gen).output) = 0 := by
  exact (scored_prefixRatio_tendsto gen).limsup_eq

 theorem negative_claim : NegativeClaim := by
  intro gen _
  refine ⟨target gen, target_in_class gen, presenter gen, tr gen, orderedTarget gen, ?_⟩
  exact ⟨rfl, orderedTarget_inherits gen, presented_by gen, follows_protocol gen,
    clean_presentation gen, injective_presentation gen, complete_presentation gen,
    scored_density_zero gen⟩

end
end Stage3Work
