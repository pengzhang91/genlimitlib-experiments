import Stage3Model
import Mathlib.Data.Nat.Nth
import GenLimit.Paper39_DenseGeneration.Abstract.Density

open Set

namespace Stage3S2B

structure Hist (t : ℕ) where
  x : Fin t → ℕ
  q : Fin t → Option ℕ
  a : Fin t → Option Bool
  y : Fin t → ℕ

namespace Hist

def empty : Hist 0 where
  x := Fin.elim0
  q := Fin.elim0
  a := Fin.elim0
  y := Fin.elim0

lemma ordinary_infinite_aux : ordinary.Infinite := by
  have hodd : Set.range (fun n : ℕ => 2 * n + 3) ⊆ ordinary := by
    intro z hz
    obtain ⟨n, rfl⟩ := hz
    intro hcore
    obtain ⟨k, hk⟩ := hcore
    dsimp at hk
    cases k with
    | zero => simp at hk
    | succ k =>
        have heven : Even (2 ^ (Nat.succ k)) :=
          Nat.even_pow.mpr ⟨even_two, by omega⟩
        have heven' : Even (2 * n + 3) := by rw [← hk]; exact heven
        have hodd' : Odd (2 * n + 3) := ⟨n + 1, by omega⟩
        obtain ⟨a, ha⟩ := heven'
        obtain ⟨b, hb⟩ := hodd'
        omega
  have hinj : Function.Injective (fun n : ℕ => 2 * n + 3) := by
    intro a b hab
    dsimp at hab
    omega
  exact (Set.infinite_range_of_injective hinj).mono hodd

def bad {t : ℕ} (h : Hist t) : Set ℕ :=
  Set.range h.x ∪ {z | ∃ i, h.q i = some z} ∪ Set.range h.y

lemma bad_finite {t : ℕ} (h : Hist t) : (bad h).Finite := by
  have hq : {z | ∃ i, h.q i = some z} ⊆
      Set.range (fun i => (h.q i).getD 0) := by
    intro z hz
    obtain ⟨i, hi⟩ := hz
    refine ⟨i, ?_⟩
    simp [hi]
  exact ((Set.finite_range h.x).union ((Set.finite_range _).subset hq)).union
    (Set.finite_range h.y)

lemma candidate_exists {t : ℕ} (h : Hist t) :
    ∃ z, z ∈ ordinary ∧ z ∉ bad h := by
  obtain ⟨z, hz, hnot⟩ := ordinary_infinite_aux.exists_notMem_finset (bad_finite h).toFinset
  exact ⟨z, hz, by simpa using hnot⟩

noncomputable def candidate {t : ℕ} (h : Hist t) : ℕ := by
  classical
  exact Nat.find (candidate_exists h)

lemma candidate_spec {t : ℕ} (h : Hist t) :
    candidate h ∈ ordinary ∧
    candidate h ∉ Set.range h.x ∧
    (∀ i, h.q i ≠ some (candidate h)) ∧
    candidate h ∉ Set.range h.y := by
  classical
  unfold candidate
  have hs := Nat.find_spec (candidate_exists h)
  refine ⟨hs.1, ?_, ?_, ?_⟩
  · intro hz
    exact hs.2 (Or.inl (Or.inl hz))
  · intro i hi
    exact hs.2 (Or.inl (Or.inr ⟨i, hi⟩))
  · intro hz
    exact hs.2 (Or.inr hz)

noncomputable def nextX {t : ℕ} (h : Hist t) : ℕ :=
  if Even t then 2 ^ (t / 2) else candidate h

noncomputable def step (gen : FeedbackGenerator) {t : ℕ} (h : Hist t) : Hist (t + 1) := by
  classical
  let xn := nextX h
  let x' : Fin (t + 1) → ℕ := Fin.lastCases xn h.x
  let qn := gen.query t x' h.a
  let an : Option Bool := match qn with
    | none => none
    | some z => some (decide (z ∈ core ∨ ∃ i, x' i = z))
  let a' : Fin (t + 1) → Option Bool := Fin.lastCases an h.a
  let yn := gen.output t x' a'
  exact {
    x := x'
    q := Fin.lastCases qn h.q
    a := a'
    y := Fin.lastCases yn h.y
  }

noncomputable def run (gen : FeedbackGenerator) : (t : ℕ) → Hist t
  | 0 => empty
  | t + 1 => step gen (run gen t)

lemma run_succ_x_last (gen : FeedbackGenerator) (t : ℕ) :
    (run gen (t + 1)).x (Fin.last t) = nextX (run gen t) := by
  simp [run, step]

lemma run_succ_q_last (gen : FeedbackGenerator) (t : ℕ) :
    (run gen (t + 1)).q (Fin.last t) = gen.query t (run gen (t + 1)).x (run gen t).a := by
  simp [run, step]

lemma run_succ_old_x (gen : FeedbackGenerator) (t : ℕ) (i : Fin t) :
    (run gen (t + 1)).x i.castSucc = (run gen t).x i := by
  simp [run, step]

lemma run_succ_old_q (gen : FeedbackGenerator) (t : ℕ) (i : Fin t) :
    (run gen (t + 1)).q i.castSucc = (run gen t).q i := by
  simp [run, step]

lemma run_succ_old_a (gen : FeedbackGenerator) (t : ℕ) (i : Fin t) :
    (run gen (t + 1)).a i.castSucc = (run gen t).a i := by
  simp [run, step]

lemma run_succ_old_y (gen : FeedbackGenerator) (t : ℕ) (i : Fin t) :
    (run gen (t + 1)).y i.castSucc = (run gen t).y i := by
  simp [run, step]

end Hist

end Stage3S2B

namespace Stage3S2B
namespace Hist

lemma run_x_eq_last (gen : FeedbackGenerator) :
    ∀ (n : ℕ) (i : Fin n),
      (run gen n).x i = (run gen (i.1 + 1)).x (Fin.last i.1)
  | 0, i => Fin.elim0 i
  | n + 1, i => by
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rfl
      · rw [run_succ_old_x]
        exact run_x_eq_last gen n j

lemma run_q_eq_last (gen : FeedbackGenerator) :
    ∀ (n : ℕ) (i : Fin n),
      (run gen n).q i = (run gen (i.1 + 1)).q (Fin.last i.1)
  | 0, i => Fin.elim0 i
  | n + 1, i => by
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rfl
      · rw [run_succ_old_q]
        exact run_q_eq_last gen n j

lemma run_a_eq_last (gen : FeedbackGenerator) :
    ∀ (n : ℕ) (i : Fin n),
      (run gen n).a i = (run gen (i.1 + 1)).a (Fin.last i.1)
  | 0, i => Fin.elim0 i
  | n + 1, i => by
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rfl
      · rw [run_succ_old_a]
        exact run_a_eq_last gen n j

lemma run_y_eq_last (gen : FeedbackGenerator) :
    ∀ (n : ℕ) (i : Fin n),
      (run gen n).y i = (run gen (i.1 + 1)).y (Fin.last i.1)
  | 0, i => Fin.elim0 i
  | n + 1, i => by
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rfl
      · rw [run_succ_old_y]
        exact run_y_eq_last gen n j

noncomputable def transcript (gen : FeedbackGenerator) : Transcript where
  presentation t := (run gen (t + 1)).x (Fin.last t)
  query t := (run gen (t + 1)).q (Fin.last t)
  answer t := (run gen (t + 1)).a (Fin.last t)
  output t := (run gen (t + 1)).y (Fin.last t)

lemma transcript_x_prefix (gen : FeedbackGenerator) (t : ℕ) :
    (fun i : Fin t => (transcript gen).presentation i) = (run gen t).x := by
  funext i
  exact (run_x_eq_last gen t i).symm

lemma transcript_q_prefix (gen : FeedbackGenerator) (t : ℕ) :
    (fun i : Fin t => (transcript gen).query i) = (run gen t).q := by
  funext i
  exact (run_q_eq_last gen t i).symm

lemma transcript_a_prefix (gen : FeedbackGenerator) (t : ℕ) :
    (fun i : Fin t => (transcript gen).answer i) = (run gen t).a := by
  funext i
  exact (run_a_eq_last gen t i).symm

lemma transcript_y_prefix (gen : FeedbackGenerator) (t : ℕ) :
    (fun i : Fin t => (transcript gen).output i) = (run gen t).y := by
  funext i
  exact (run_y_eq_last gen t i).symm

lemma transcript_x_even (gen : FeedbackGenerator) {t : ℕ} (ht : Even t) :
    (transcript gen).presentation t = 2 ^ (t / 2) := by
  change (run gen (t + 1)).x (Fin.last t) = _
  rw [run_succ_x_last]
  simp [nextX, ht]

lemma transcript_x_odd (gen : FeedbackGenerator) {t : ℕ} (ht : ¬ Even t) :
    (transcript gen).presentation t = candidate (run gen t) := by
  change (run gen (t + 1)).x (Fin.last t) = _
  rw [run_succ_x_last]
  simp [nextX, ht]

lemma transcript_x_odd_ordinary (gen : FeedbackGenerator) {t : ℕ} (ht : ¬ Even t) :
    (transcript gen).presentation t ∈ ordinary := by
  rw [transcript_x_odd gen ht]
  exact (candidate_spec (run gen t)).1

noncomputable def adversarialTarget (gen : FeedbackGenerator) : Language :=
  core ∪ Set.range (transcript gen).presentation

lemma core_presented (gen : FeedbackGenerator) (k : ℕ) :
    ∃ t, (transcript gen).presentation t = 2 ^ k := by
  refine ⟨2 * k, ?_⟩
  rw [transcript_x_even gen (even_two_mul k)]
  congr
  omega

lemma target_complete (gen : FeedbackGenerator) :
    Complete (transcript gen).presentation (adversarialTarget gen) := by
  intro z hz
  rcases hz with hz | hz
  · obtain ⟨k, rfl⟩ := hz
    exact core_presented gen k
  · exact hz

lemma target_clean (gen : FeedbackGenerator) :
    Clean (transcript gen).presentation (adversarialTarget gen) := by
  intro t
  exact Or.inr ⟨t, rfl⟩

lemma target_mem_class (gen : FeedbackGenerator) :
    adversarialTarget gen ∈ targetClass := by
  refine ⟨Set.range (transcript gen).presentation ∩ ordinary, Set.inter_subset_right, ?_⟩
  ext z
  constructor
  · intro hz
    rcases hz with hz | hz
    · exact Or.inl hz
    · by_cases hc : z ∈ core
      · exact Or.inl hc
      · exact Or.inr ⟨hz, hc⟩
  · intro hz
    rcases hz with hz | hz
    · exact Or.inl hz
    · exact Or.inr hz.1

end Hist
end Stage3S2B

namespace Stage3S2B
namespace Hist

lemma run_succ_a_last (gen : FeedbackGenerator) (t : ℕ) :
    (run gen (t + 1)).a (Fin.last t) =
      match gen.query t (run gen (t + 1)).x (run gen t).a with
      | none => none
      | some z => some (by classical exact decide (z ∈ core ∨ ∃ i, (run gen (t + 1)).x i = z)) := by
  classical
  simp [run, step]

lemma run_succ_y_last (gen : FeedbackGenerator) (t : ℕ) :
    (run gen (t + 1)).y (Fin.last t) =
      gen.output t (run gen (t + 1)).x (run gen (t + 1)).a := by
  simp [run, step]

lemma query_avoids_future_ordinary (gen : FeedbackGenerator) {t s z : ℕ}
    (hts : t < s) (hq : (transcript gen).query t = some z)
    (hz : z ∈ ordinary) : (transcript gen).presentation s ≠ z := by
  by_cases hs : Even s
  · rw [transcript_x_even gen hs]
    intro heq
    exact hz ⟨s / 2, heq⟩
  · rw [transcript_x_odd gen hs]
    have hav := (candidate_spec (run gen s)).2.2.1 ⟨t, hts⟩
    intro heq
    apply hav
    have hp := congrFun (transcript_q_prefix gen s) ⟨t, hts⟩
    calc
      (run gen s).q ⟨t, hts⟩ = (transcript gen).query t := hp.symm
      _ = some z := hq
      _ = some (candidate (run gen s)) := congrArg some heq.symm

lemma output_avoids_future_ordinary (gen : FeedbackGenerator) {t s z : ℕ}
    (hts : t < s) (hy : (transcript gen).output t = z)
    (hz : z ∈ ordinary) : (transcript gen).presentation s ≠ z := by
  by_cases hs : Even s
  · rw [transcript_x_even gen hs]
    intro heq
    exact hz ⟨s / 2, heq⟩
  · rw [transcript_x_odd gen hs]
    have hav := (candidate_spec (run gen s)).2.2.2
    intro heq
    apply hav
    refine ⟨⟨t, hts⟩, ?_⟩
    have hp := congrFun (transcript_y_prefix gen s) ⟨t, hts⟩
    calc
      (run gen s).y ⟨t, hts⟩ = (transcript gen).output t := hp.symm
      _ = z := hy
      _ = candidate (run gen s) := heq.symm

lemma presentation_injective (gen : FeedbackGenerator) :
    Function.Injective (transcript gen).presentation := by
  intro s t hst
  apply le_antisymm
  · by_contra hnot
    have hts : t < s := Nat.lt_of_not_ge hnot
    by_cases hs : Even s
    · by_cases ht : Even t
      · rw [transcript_x_even gen hs, transcript_x_even gen ht] at hst
        have hdiv : t / 2 < s / 2 := by
          obtain ⟨a, ha⟩ := ht
          obtain ⟨b, hb⟩ := hs
          omega
        have heq : s / 2 = t / 2 :=
          Nat.pow_right_injective (by omega : 1 < 2) hst
        omega
      · have hord := transcript_x_odd_ordinary gen ht
        rw [← hst, transcript_x_even gen hs] at hord
        exact hord ⟨s / 2, rfl⟩
    · rw [transcript_x_odd gen hs] at hst
      have hav := (candidate_spec (run gen s)).2.1
      apply hav
      refine ⟨⟨t, hts⟩, ?_⟩
      have hp := congrFun (transcript_x_prefix gen s) ⟨t, hts⟩
      exact hp.symm.trans hst.symm
  · by_contra hnot
    have hst' : s < t := Nat.lt_of_not_ge hnot
    by_cases ht : Even t
    · by_cases hs : Even s
      · rw [transcript_x_even gen hs, transcript_x_even gen ht] at hst
        have hdiv : s / 2 < t / 2 := by
          obtain ⟨a, ha⟩ := hs
          obtain ⟨b, hb⟩ := ht
          omega
        have heq : s / 2 = t / 2 :=
          Nat.pow_right_injective (by omega : 1 < 2) hst
        omega
      · have hord := transcript_x_odd_ordinary gen hs
        rw [hst, transcript_x_even gen ht] at hord
        exact hord ⟨t / 2, rfl⟩
    · rw [transcript_x_odd gen ht] at hst
      have hav := (candidate_spec (run gen t)).2.1
      apply hav
      refine ⟨⟨s, hst'⟩, ?_⟩
      have hp := congrFun (transcript_x_prefix gen t) ⟨s, hst'⟩
      exact hp.symm.trans hst

lemma query_answer_exact (gen : FeedbackGenerator) (t : ℕ) (z : ℕ)
    (hq : (transcript gen).query t = some z) :
    z ∈ adversarialTarget gen ↔
      z ∈ core ∨ ∃ i : Fin (t + 1), (run gen (t + 1)).x i = z := by
  constructor
  · intro hz
    rcases hz with hz | hz
    · exact Or.inl hz
    · obtain ⟨s, hs⟩ := hz
      by_cases hst : s ≤ t
      · right
        let i : Fin (t + 1) := ⟨s, Nat.lt_succ_iff.mpr hst⟩
        refine ⟨i, ?_⟩
        have hp := congrFun (transcript_x_prefix gen (t + 1)) i
        exact hp.symm.trans hs
      · by_cases hcore : z ∈ core
        · exact Or.inl hcore
        · have hzord : z ∈ ordinary := hcore
          exact False.elim ((query_avoids_future_ordinary gen (Nat.lt_of_not_ge hst) hq hzord) hs)
  · intro hz
    rcases hz with hz | ⟨i, hi⟩
    · exact Or.inl hz
    · right
      refine ⟨i.1, ?_⟩
      have hp := congrFun (transcript_x_prefix gen (t + 1)) i
      exact hp.trans hi

end Hist
end Stage3S2B

namespace Stage3S2B
namespace Hist

lemma follows_protocol (gen : FeedbackGenerator) :
    FollowsProtocol gen (adversarialTarget gen) (transcript gen) := by
  intro t
  have hx := transcript_x_prefix gen (t + 1)
  have ha := transcript_a_prefix gen t
  have hq : (transcript gen).query t =
      gen.query t (fun i => (transcript gen).presentation i)
        (fun i => (transcript gen).answer i) := by
    change (run gen (t + 1)).q (Fin.last t) = _
    rw [run_succ_q_last]
    rw [hx, ha]
  refine ⟨hq, ?_, ?_⟩
  · rw [hq]
    generalize hqn : gen.query t (fun i => (transcript gen).presentation i)
        (fun i => (transcript gen).answer i) = qn
    cases qn with
    | none =>
        change (run gen (t + 1)).a (Fin.last t) = none
        rw [run_succ_a_last]
        have hqin : gen.query t (run gen (t + 1)).x (run gen t).a = none := by
          simpa [← hx, ← ha] using hqn
        rw [hqin]
    | some z =>
        change (run gen (t + 1)).a (Fin.last t) =
          some (membershipAnswer (adversarialTarget gen) z)
        rw [run_succ_a_last]
        have hqtr : (transcript gen).query t = some z := hq.trans hqn
        have hiff := query_answer_exact gen t z hqtr
        have hqin : gen.query t (run gen (t + 1)).x (run gen t).a = some z := by
          simpa [← hx, ← ha] using hqn
        rw [hqin]
        unfold membershipAnswer
        congr 1
        by_cases hleft : z ∈ core ∨ ∃ i : Fin (t + 1), (run gen (t + 1)).x i = z
        · have hright : z ∈ adversarialTarget gen := hiff.mpr hleft
          simp [hleft, hright]
        · have hright : z ∉ adversarialTarget gen := fun hz => hleft (hiff.mp hz)
          simp [hleft, hright]
  · change (run gen (t + 1)).y (Fin.last t) = _
    rw [run_succ_y_last]
    rw [transcript_x_prefix gen (t + 1), transcript_a_prefix gen (t + 1)]

noncomputable def presenter (gen : FeedbackGenerator) : CausalPresenter where
  next t _ _ _ _ := (transcript gen).presentation t

lemma presented_by (gen : FeedbackGenerator) :
    PresentedBy (presenter gen) (transcript gen) := by
  intro t
  rfl

lemma scored_subset_core (gen : FeedbackGenerator) :
    scored (adversarialTarget gen) (transcript gen).presentation
      (transcript gen).output ⊆ core := by
  intro z hz
  rcases hz with ⟨hzK, t, hyt, hnot⟩
  by_contra hzcore
  have hzord : z ∈ ordinary := hzcore
  rcases hzK with hzcore' | ⟨s, hxs⟩
  · exact hzcore hzcore'
  · have hts : t < s := by
      by_contra hnotlt
      apply hnot
      exact ⟨s, Nat.le_of_not_gt hnotlt, hxs⟩
    exact (output_avoids_future_ordinary gen hts hyt hzord) hxs

end Hist
end Stage3S2B

namespace Stage3S2B
namespace Hist

lemma candidate_le {t : ℕ} (h : Hist t) : candidate h ≤ 6 * t + 3 := by
  classical
  let xs : Finset ℕ := Finset.univ.image h.x
  let qs : Finset ℕ := Finset.univ.image (fun i => (h.q i).getD 0)
  let ys : Finset ℕ := Finset.univ.image h.y
  let bs : Finset ℕ := xs ∪ qs ∪ ys
  let cs : Finset ℕ := (Finset.range (3 * t + 1)).image (fun n => 2 * n + 3)
  have hxs : xs.card ≤ t := by
    simpa [xs] using Finset.card_image_le (s := (Finset.univ : Finset (Fin t))) (f := h.x)
  have hqs : qs.card ≤ t := by
    simpa [qs] using Finset.card_image_le (s := (Finset.univ : Finset (Fin t)))
      (f := fun i => (h.q i).getD 0)
  have hys : ys.card ≤ t := by
    simpa [ys] using Finset.card_image_le (s := (Finset.univ : Finset (Fin t))) (f := h.y)
  have hbs : bs.card ≤ 3 * t := by
    calc
      bs.card ≤ (xs ∪ qs).card + ys.card := Finset.card_union_le _ _
      _ ≤ (xs.card + qs.card) + ys.card := Nat.add_le_add_right (Finset.card_union_le _ _) _
      _ ≤ t + t + t := by omega
      _ = 3 * t := by omega
  have hcs : cs.card = 3 * t + 1 := by
    simp only [cs]
    rw [Finset.card_image_iff.mpr]
    · simp
    · intro a ha b hb hab
      dsimp at hab
      omega
  obtain ⟨z, hzcs, hzbs⟩ := Finset.exists_mem_notMem_of_card_lt_card (by omega : bs.card < cs.card)
  simp only [cs, Finset.mem_image] at hzcs
  obtain ⟨j, hj, rfl⟩ := hzcs
  have hjlt : j < 3 * t + 1 := Finset.mem_range.mp hj
  have hord : 2 * j + 3 ∈ ordinary := by
    intro hcore
    obtain ⟨k, hk⟩ := hcore
    dsimp at hk
    cases k with
    | zero => simp at hk
    | succ k =>
        have heven : Even (2 ^ (Nat.succ k)) := Nat.even_pow.mpr ⟨even_two, by omega⟩
        have heven' : Even (2 * j + 3) := by rw [← hk]; exact heven
        have hodd : Odd (2 * j + 3) := ⟨j + 1, by omega⟩
        obtain ⟨a, ha⟩ := heven'
        obtain ⟨b, hb⟩ := hodd
        omega
  have hnotbad : 2 * j + 3 ∉ bad h := by
    intro hbad
    apply hzbs
    rcases hbad with (hx | hq) | hy
    · simp only [bs, Finset.mem_union]
      exact Or.inl (Or.inl (by simpa [xs] using hx))
    · simp only [bs, Finset.mem_union]
      left
      right
      obtain ⟨i, hi⟩ := hq
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, by simp [qs, hi]⟩
    · simp only [bs, Finset.mem_union]
      right
      simpa [ys] using hy
  unfold candidate
  exact (Nat.find_le ⟨hord, hnotbad⟩).trans (by omega)

end Hist
end Stage3S2B

namespace Stage3S2B
namespace Hist

lemma core_infinite_aux : core.Infinite := by
  exact Set.infinite_range_of_injective
    (Nat.pow_right_injective (by omega : 1 < 2))

lemma target_infinite' (gen : FeedbackGenerator) : (adversarialTarget gen).Infinite := by
  exact core_infinite_aux.mono (fun z hz => Or.inl hz)

noncomputable def orderedTarget (gen : FeedbackGenerator) : OrderedLanguage where
  carrier := adversarialTarget gen
  enumeration := Nat.nth (fun z => z ∈ adversarialTarget gen)
  enumeration_injective := Nat.nth_injective (target_infinite' gen)
  range_enumeration := Nat.range_nth_of_infinite (target_infinite' gen)

lemma orderedTarget_carrier (gen : FeedbackGenerator) :
    (orderedTarget gen).carrier = adversarialTarget gen := rfl

lemma orderedTarget_strictMono (gen : FeedbackGenerator) :
    InheritsAmbientOrder (orderedTarget gen) := by
  exact Nat.nth_strictMono (target_infinite' gen)

end Hist
end Stage3S2B

namespace Stage3S2B
namespace Hist

lemma odd_presentation_le (gen : FeedbackGenerator) (j : ℕ) :
    (transcript gen).presentation (2 * j + 1) ≤ 12 * j + 9 := by
  have hodd : ¬ Even (2 * j + 1) := by
    intro h
    obtain ⟨k, hk⟩ := h
    omega
  rw [transcript_x_odd gen hodd]
  exact (candidate_le (run gen (2 * j + 1))).trans (by omega)

lemma ordered_enumeration_le (gen : FeedbackGenerator) (n : ℕ) :
    (orderedTarget gen).enumeration n ≤ 12 * n + 9 := by
  by_contra hle
  have hgt : 12 * n + 9 < (orderedTarget gen).enumeration n := Nat.lt_of_not_ge hle
  letI : Infinite (adversarialTarget gen) :=
    Set.infinite_coe_iff.mpr (target_infinite' gen)
  let e : ℕ ≃o (adversarialTarget gen) :=
    Nat.Subtype.orderIsoOfNat (adversarialTarget gen)
  let f : Fin (n + 1) → Fin n := fun j => by
    let z := (transcript gen).presentation (2 * j.1 + 1)
    have hzK : z ∈ adversarialTarget gen := Or.inr ⟨2 * j.1 + 1, rfl⟩
    let r := e.symm ⟨z, hzK⟩
    refine ⟨r, ?_⟩
    have hzle : z ≤ 12 * n + 9 :=
      (odd_presentation_le gen j.1).trans (by omega)
    have hrval : ((e r : adversarialTarget gen) : ℕ) = z := by
      exact congrArg Subtype.val (e.apply_symm_apply ⟨z, hzK⟩)
    have henv : ((e n : adversarialTarget gen) : ℕ) =
        (orderedTarget gen).enumeration n := by
      symm
      exact Nat.nth_apply_eq_orderIsoOfNat (target_infinite' gen) n
    have hltval : ((e r : adversarialTarget gen) : ℕ) <
        ((e n : adversarialTarget gen) : ℕ) := by
      rw [hrval, henv]
      exact hzle.trans_lt hgt
    exact (e.lt_iff_lt.mp (Subtype.coe_lt_coe.mp hltval))
  have hf : Function.Injective f := by
    intro i j hij
    have hrank : (f i : ℕ) = (f j : ℕ) := congrArg Fin.val hij
    dsimp [f] at hrank
    have heqsub := congrArg e hrank
    simp only [e.apply_symm_apply] at heqsub
    have heqz : (transcript gen).presentation (2 * i.1 + 1) =
        (transcript gen).presentation (2 * j.1 + 1) :=
      congrArg Subtype.val heqsub
    have ht := presentation_injective gen heqz
    apply Fin.ext
    omega
  have hcard := Fintype.card_le_of_injective f hf
  simp at hcard

end Hist
end Stage3S2B

namespace Stage3S2B
namespace Hist

lemma core_prefixCount_le (gen : FeedbackGenerator) (n : ℕ) :
    (orderedTarget gen).prefixCount core n ≤ Nat.log2 (12 * n + 9) + 1 := by
  classical
  unfold GenLimit.KleinbergWei.OrderedLanguage.prefixCount
  let s := (Finset.range n).filter fun i => (orderedTarget gen).enumeration i ∈ core
  let f : ℕ → ℕ := fun i => Nat.log2 ((orderedTarget gen).enumeration i)
  have hcard : s.card ≤ (Finset.range (Nat.log2 (12 * n + 9) + 1)).card := by
    apply Finset.card_le_card_of_injOn f
    · intro i hi
      change i ∈ s at hi
      rw [Finset.mem_filter] at hi
      have hin : i < n := Finset.mem_range.mp hi.1
      obtain ⟨k, hk⟩ := hi.2
      have henum : (orderedTarget gen).enumeration i = 2 ^ k := hk.symm
      have hbound : 2 ^ k ≤ 12 * n + 9 := by
        rw [← henum]
        exact (ordered_enumeration_le gen i).trans (by omega : 12 * i + 9 ≤ 12 * n + 9)
      have hklog : k ≤ Nat.log2 (12 * n + 9) :=
        (Nat.le_log2 (by omega : 12 * n + 9 ≠ 0)).mpr hbound
      apply Finset.mem_range.mpr
      simp only [f, henum, Nat.log2_two_pow]
      omega
    · intro i hi j hj hfij
      change i ∈ s at hi
      change j ∈ s at hj
      rw [Finset.mem_filter] at hi hj
      obtain ⟨ki, hki⟩ := hi.2
      obtain ⟨kj, hkj⟩ := hj.2
      have hk : ki = kj := by
        simpa [f, ← hki, ← hkj] using hfij
      apply (orderedTarget gen).enumeration_injective
      rw [← hki, ← hkj, hk]
  simpa [s] using hcard

end Hist
end Stage3S2B

open Filter
open scoped Topology

namespace Stage3S2B
namespace Hist

lemma tendsto_log_bound_div : Tendsto
    (fun n : ℕ => ((Nat.log2 (12 * n + 9) + 1 : ℕ) : ℝ) / (n : ℝ))
    atTop (𝓝 0) := by
  have hlogb : Tendsto
      (fun n : ℕ => Real.logb 2 (12 * (n : ℝ) + 9) / (n : ℝ))
      atTop (𝓝 0) := by
    have hk0 : Tendsto (fun n : ℕ => 12 * (n : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num : (0 : ℝ) < 12)
    have hk : Tendsto (fun n : ℕ => 12 * (n : ℝ) + 9) atTop atTop :=
      tendsto_atTop_add_const_right atTop 9 hk0
    have hz :=
      ((Real.isLittleO_logb_id_atTop (b := (2 : ℝ))).comp_tendsto hk).tendsto_div_nhds_zero
    have h9 : Tendsto (fun n : ℕ => (9 : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    have hratio' : Tendsto
        (fun n : ℕ => (12 : ℝ) + 9 / (n : ℝ)) atTop (𝓝 12) := by
      simpa using tendsto_const_nhds.add h9
    have hratio : Tendsto
        (fun n : ℕ => (12 * (n : ℝ) + 9) / (n : ℝ)) atTop (𝓝 12) := by
      apply hratio'.congr'
      filter_upwards [eventually_ne_atTop 0] with n hn
      field_simp
    have hmul := hz.mul hratio
    simp only [zero_mul] at hmul
    apply hmul.congr'
    filter_upwards [eventually_ne_atTop 0] with n hn
    dsimp only [Function.comp_apply, id_eq]
    field_simp
  have hnat : Tendsto
      (fun n : ℕ => (Nat.log2 (12 * n + 9) : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
    exact squeeze_zero
      (fun n => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      (fun n => by
        apply div_le_div_of_nonneg_right
        · simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using
            (Real.log2_le_logb (12 * n + 9))
        · exact Nat.cast_nonneg _)
      hlogb
  have hone : Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  simpa only [Nat.cast_add, Nat.cast_one, add_div, zero_add] using hnat.add hone

lemma core_prefixRatio_tendsto (gen : FeedbackGenerator) :
    Tendsto ((orderedTarget gen).prefixRatio core) atTop (𝓝 0) := by
  exact squeeze_zero
    (fun n => (orderedTarget gen).prefixRatio_nonneg core n)
    (fun n => by
      by_cases hn : n = 0
      · simp [hn]
      · unfold GenLimit.KleinbergWei.OrderedLanguage.prefixRatio
        simp only [hn, if_false]
        apply div_le_div_of_nonneg_right
        · exact_mod_cast core_prefixCount_le gen n
        · exact Nat.cast_nonneg n)
    tendsto_log_bound_div

lemma core_upperDensity_zero (gen : FeedbackGenerator) :
    (orderedTarget gen).upperDensity core = 0 := by
  unfold GenLimit.KleinbergWei.OrderedLanguage.upperDensity
  exact (core_prefixRatio_tendsto gen).limsup_eq

lemma scored_upperDensity_zero (gen : FeedbackGenerator) :
    (orderedTarget gen).upperDensity
        (scored (adversarialTarget gen) (transcript gen).presentation
          (transcript gen).output) = 0 := by
  apply le_antisymm
  · calc
      (orderedTarget gen).upperDensity
          (scored (adversarialTarget gen) (transcript gen).presentation
            (transcript gen).output) ≤
          (orderedTarget gen).upperDensity core :=
        (orderedTarget gen).upperDensity_mono (scored_subset_core gen)
      _ = 0 := core_upperDensity_zero gen
  · exact (orderedTarget gen).upperDensity_nonneg _

lemma negative_claim : NegativeClaim := by
  intro gen _
  refine ⟨adversarialTarget gen, target_mem_class gen,
    presenter gen, transcript gen, orderedTarget gen, ?_⟩
  exact ⟨orderedTarget_carrier gen, orderedTarget_strictMono gen,
    presented_by gen, follows_protocol gen, target_clean gen,
    presentation_injective gen, target_complete gen, scored_upperDensity_zero gen⟩

end Hist
end Stage3S2B
