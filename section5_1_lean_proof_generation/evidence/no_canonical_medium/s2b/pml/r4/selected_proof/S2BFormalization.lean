import Stage3Model
import Mathlib.Data.Nat.Nth
import GenLimit.Paper17_InfiniteContamination.SharedVanishingPresentation

open Set Function Filter

namespace Stage3Proof

open Stage3S2B

lemma candidate_injective : Function.Injective (fun n : ℕ => 2 * n + 3) := by
  intro a b h
  dsimp at h
  omega

lemma candidate_ordinary (n : ℕ) : 2 * n + 3 ∈ ordinary := by
  intro h
  rcases h with ⟨k, hk⟩
  by_cases hk0 : k = 0
  · subst k
    norm_num at hk
  · have heven : Even (2 ^ k) := by
      exact Nat.even_pow.mpr ⟨by norm_num, hk0⟩
    have hodd : Odd (2 * n + 3) := ⟨n + 1, by omega⟩
    have : Even (2 * n + 3) := by simpa [hk] using heven
    exact (Nat.not_even_iff_odd.mpr hodd) this

lemma core_injective : Function.Injective (fun k : ℕ => 2 ^ k) := by
  exact Nat.pow_right_injective (by omega)

lemma targetClass_uncountable : ¬ targetClass.Countable := by
  intro hcount
  obtain ⟨f, hf⟩ := Set.countable_iff_exists_subset_range.mp hcount
  let A : Language := {z | ∃ n, z = 2 * n + 3 ∧ z ∉ f n}
  let K : Language := core ∪ A
  have hA : A ⊆ ordinary := by
    intro z hz
    rcases hz with ⟨n, rfl, _⟩
    exact candidate_ordinary n
  have hK : K ∈ targetClass := ⟨A, hA, rfl⟩
  obtain ⟨n, hn⟩ := hf hK
  have hcand : 2 * n + 3 ∉ core := candidate_ordinary n
  have hdiag : (2 * n + 3 ∈ K) ↔ (2 * n + 3 ∉ f n) := by
    simp [K, A, hcand]
  rw [← hn] at hdiag
  by_cases hmem : 2 * n + 3 ∈ f n
  · exact (hdiag.mp hmem) hmem
  · exact hmem (hdiag.mpr hmem)

lemma uniformly_generatable : UniformlyGeneratableWithoutSamples := by
  refine ⟨fun k => 2 ^ k, core_injective, 0, ?_⟩
  intro K hK t _
  rcases hK with ⟨A, hA, rfl⟩
  exact Or.inl ⟨t, rfl⟩


def snoc {α : Type} {t : ℕ} (f : Fin t → α) (x : α) : Fin (t + 1) → α :=
  fun i => if h : i.1 < t then f ⟨i.1, h⟩ else x

@[simp] lemma snoc_castSucc {α : Type} {t : ℕ} (f : Fin t → α) (x : α) (i : Fin t) :
    snoc f x i.castSucc = f i := by
  simp [snoc, i.2]

@[simp] lemma snoc_last {α : Type} {t : ℕ} (f : Fin t → α) (x : α) :
    snoc f x (Fin.last t) = x := by
  simp [snoc]

structure Hist (t : ℕ) where
  presentation : Fin t → ℕ
  query : Fin t → Option ℕ
  answer : Fin t → Option Bool
  output : Fin t → ℕ
  forbidden : Finset ℕ

noncomputable def blocked {t : ℕ} (h : Hist t) : Finset ℕ :=
  h.forbidden ∪ Finset.univ.image h.presentation

lemma exists_candidate_not_blocked {t : ℕ} (h : Hist t) :
    ∃ n, 2 * n + 3 ∉ blocked h := by
  obtain ⟨z, ⟨n, rfl⟩, hz⟩ :=
    (Set.infinite_range_of_injective candidate_injective).exists_not_mem_finset (blocked h)
  exact ⟨n, hz⟩

noncomputable def freshIndex {t : ℕ} (h : Hist t) : ℕ :=
  Nat.find (exists_candidate_not_blocked h)

noncomputable def freshOrd {t : ℕ} (h : Hist t) : ℕ :=
  2 * freshIndex h + 3

lemma freshOrd_not_blocked {t : ℕ} (h : Hist t) : freshOrd h ∉ blocked h := by
  exact Nat.find_spec (exists_candidate_not_blocked h)

lemma freshOrd_ordinary {t : ℕ} (h : Hist t) : freshOrd h ∈ ordinary :=
  candidate_ordinary _

noncomputable def nextPresentation (t : ℕ) (h : Hist t) : ℕ :=
  if Even t then 2 ^ (t / 2) else freshOrd h

noncomputable def currentQuery (gen : FeedbackGenerator) (t : ℕ) (h : Hist t)
    (x : ℕ) : Option ℕ :=
  gen.query t (snoc h.presentation x) h.answer

noncomputable def currentAnswer (t : ℕ) (h : Hist t) (x : ℕ)
    (q : Option ℕ) : Option Bool := by
  classical
  exact q.map fun z => decide (z ∈ core ∨ z = x ∨ ∃ i, h.presentation i = z)

noncomputable def currentOutput (gen : FeedbackGenerator) (t : ℕ) (h : Hist t)
    (x : ℕ) (a : Option Bool) : ℕ :=
  gen.output t (snoc h.presentation x) (snoc h.answer a)

noncomputable def banIfFreshOrdinary {t : ℕ} (h : Hist t) (x z : ℕ)
    (s : Finset ℕ) : Finset ℕ := by
  classical
  exact if z ∈ ordinary ∧ z ≠ x ∧ ∀ i, h.presentation i ≠ z then insert z s else s

noncomputable def queryBan {t : ℕ} (h : Hist t) (q : Option ℕ)
    (a : Option Bool) : Finset ℕ :=
  match q, a with
  | some z, some false => insert z h.forbidden
  | _, _ => h.forbidden

noncomputable def nextForbidden {t : ℕ} (h : Hist t) (x : ℕ)
    (q : Option ℕ) (a : Option Bool) (y : ℕ) : Finset ℕ :=
  banIfFreshOrdinary h x y (queryBan h q a)

noncomputable def step (gen : FeedbackGenerator) (t : ℕ) (h : Hist t) : Hist (t + 1) := by
  let x := nextPresentation t h
  let q := currentQuery gen t h x
  let a := currentAnswer t h x q
  let y := currentOutput gen t h x a
  let fy := nextForbidden h x q a y
  exact {
    presentation := snoc h.presentation x
    query := snoc h.query q
    answer := snoc h.answer a
    output := snoc h.output y
    forbidden := fy
  }

noncomputable def history (gen : FeedbackGenerator) : (t : ℕ) → Hist t
  | 0 => {
      presentation := Fin.elim0
      query := Fin.elim0
      answer := Fin.elim0
      output := Fin.elim0
      forbidden := ∅
    }
  | t + 1 => step gen t (history gen t)

noncomputable def adversarialTranscript (gen : FeedbackGenerator) : Transcript where
  presentation t := (history gen (t + 1)).presentation (Fin.last t)
  query t := (history gen (t + 1)).query (Fin.last t)
  answer t := (history gen (t + 1)).answer (Fin.last t)
  output t := (history gen (t + 1)).output (Fin.last t)

lemma history_step (gen : FeedbackGenerator) (t : ℕ) :
    history gen (t + 1) = step gen t (history gen t) := rfl

lemma history_presentation_castSucc (gen : FeedbackGenerator) (t : ℕ) (i : Fin t) :
    (history gen (t + 1)).presentation i.castSucc = (history gen t).presentation i := by
  simp [history, step]

lemma history_query_castSucc (gen : FeedbackGenerator) (t : ℕ) (i : Fin t) :
    (history gen (t + 1)).query i.castSucc = (history gen t).query i := by
  simp [history, step]

lemma history_answer_castSucc (gen : FeedbackGenerator) (t : ℕ) (i : Fin t) :
    (history gen (t + 1)).answer i.castSucc = (history gen t).answer i := by
  simp [history, step]

lemma history_output_castSucc (gen : FeedbackGenerator) (t : ℕ) (i : Fin t) :
    (history gen (t + 1)).output i.castSucc = (history gen t).output i := by
  simp [history, step]

lemma transcript_presentation_prefix (gen : FeedbackGenerator) :
    ∀ (t : ℕ) (i : Fin t),
      (adversarialTranscript gen).presentation i = (history gen t).presentation i
  | 0, i => Fin.elim0 i
  | t + 1, i => by
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rfl
      · rw [history_presentation_castSucc]
        exact transcript_presentation_prefix gen t j

lemma transcript_query_prefix (gen : FeedbackGenerator) :
    ∀ (t : ℕ) (i : Fin t),
      (adversarialTranscript gen).query i = (history gen t).query i
  | 0, i => Fin.elim0 i
  | t + 1, i => by
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rfl
      · rw [history_query_castSucc]
        exact transcript_query_prefix gen t j

lemma transcript_answer_prefix (gen : FeedbackGenerator) :
    ∀ (t : ℕ) (i : Fin t),
      (adversarialTranscript gen).answer i = (history gen t).answer i
  | 0, i => Fin.elim0 i
  | t + 1, i => by
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rfl
      · rw [history_answer_castSucc]
        exact transcript_answer_prefix gen t j

lemma transcript_output_prefix (gen : FeedbackGenerator) :
    ∀ (t : ℕ) (i : Fin t),
      (adversarialTranscript gen).output i = (history gen t).output i
  | 0, i => Fin.elim0 i
  | t + 1, i => by
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rfl
      · rw [history_output_castSucc]
        exact transcript_output_prefix gen t j


@[simp] lemma transcript_presentation_eq (gen : FeedbackGenerator) (t : ℕ) :
    (adversarialTranscript gen).presentation t = nextPresentation t (history gen t) := by
  simp [adversarialTranscript, history, step]

@[simp] lemma transcript_query_eq (gen : FeedbackGenerator) (t : ℕ) :
    (adversarialTranscript gen).query t =
      currentQuery gen t (history gen t) (nextPresentation t (history gen t)) := by
  simp [adversarialTranscript, history, step]

@[simp] lemma transcript_answer_eq (gen : FeedbackGenerator) (t : ℕ) :
    (adversarialTranscript gen).answer t =
      currentAnswer t (history gen t) (nextPresentation t (history gen t))
        (currentQuery gen t (history gen t) (nextPresentation t (history gen t))) := by
  simp [adversarialTranscript, history, step]

@[simp] lemma transcript_output_eq (gen : FeedbackGenerator) (t : ℕ) :
    (adversarialTranscript gen).output t =
      currentOutput gen t (history gen t) (nextPresentation t (history gen t))
        (currentAnswer t (history gen t) (nextPresentation t (history gen t))
          (currentQuery gen t (history gen t) (nextPresentation t (history gen t)))) := by
  simp [adversarialTranscript, history, step]

lemma presentation_even (gen : FeedbackGenerator) {t : ℕ} (ht : Even t) :
    (adversarialTranscript gen).presentation t = 2 ^ (t / 2) := by
  simp [transcript_presentation_eq, nextPresentation, ht]

lemma presentation_odd_ordinary (gen : FeedbackGenerator) {t : ℕ} (ht : ¬ Even t) :
    (adversarialTranscript gen).presentation t ∈ ordinary := by
  simp [transcript_presentation_eq, nextPresentation, ht, freshOrd_ordinary]

lemma presentation_odd_fresh (gen : FeedbackGenerator) {t : ℕ} (ht : ¬ Even t)
    (i : Fin t) :
    (history gen t).presentation i ≠ (adversarialTranscript gen).presentation t := by
  have hnot := freshOrd_not_blocked (history gen t)
  simp only [blocked, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and,
    not_or] at hnot
  have hne := hnot.2
  simp [transcript_presentation_eq, nextPresentation, ht]
  intro heq
  exact hne ⟨i, heq⟩

lemma presentation_injective (gen : FeedbackGenerator) :
    Function.Injective (adversarialTranscript gen).presentation := by
  intro a b hab
  apply le_antisymm
  · by_contra hnot
    have hba : b < a := Nat.lt_of_not_ge hnot
    by_cases ha : Even a
    · by_cases hb : Even b
      · obtain ⟨ka, rfl⟩ := ha
        obtain ⟨kb, rfl⟩ := hb
        rw [presentation_even gen (by exact ⟨ka, rfl⟩),
          presentation_even gen (by exact ⟨kb, rfl⟩)] at hab
        have := core_injective hab.symm
        omega
      · have hord := presentation_odd_ordinary gen hb
        have hcore : (adversarialTranscript gen).presentation a ∈ core := by
          rw [presentation_even gen ha]
          exact ⟨a / 2, rfl⟩
        rw [hab] at hcore
        exact hord hcore
    · let i : Fin a := ⟨b, hba⟩
      have hfresh := presentation_odd_fresh gen ha i
      have hp := transcript_presentation_prefix gen a i
      exact hfresh (hp.symm.trans hab.symm)
  · by_contra hnot
    have hab' : a < b := Nat.lt_of_not_ge hnot
    by_cases hb : Even b
    · by_cases ha : Even a
      · obtain ⟨kb, rfl⟩ := hb
        obtain ⟨ka, rfl⟩ := ha
        rw [presentation_even gen (by exact ⟨ka, rfl⟩),
          presentation_even gen (by exact ⟨kb, rfl⟩)] at hab
        have := core_injective hab
        omega
      · have hord := presentation_odd_ordinary gen ha
        have hcore : (adversarialTranscript gen).presentation b ∈ core := by
          rw [presentation_even gen hb]
          exact ⟨b / 2, rfl⟩
        rw [← hab] at hcore
        exact hord hcore
    · let i : Fin b := ⟨a, hab'⟩
      have hfresh := presentation_odd_fresh gen hb i
      have hp := transcript_presentation_prefix gen b i
      exact hfresh (hp.symm.trans hab)

lemma presentation_core_complete (gen : FeedbackGenerator) (k : ℕ) :
    (adversarialTranscript gen).presentation (2 * k) = 2 ^ k := by
  simpa using presentation_even gen (show Even (2 * k) from ⟨k, by omega⟩)

lemma presentation_mem_core_or_ordinary (gen : FeedbackGenerator) (t : ℕ) :
    (adversarialTranscript gen).presentation t ∈ core ∪ ordinary := by
  by_cases ht : Even t
  · left
    rw [presentation_even gen ht]
    exact ⟨t / 2, rfl⟩
  · right
    exact presentation_odd_ordinary gen ht

lemma currentAnswer_some_eq (t : ℕ) (h : Hist t) (x z : ℕ) :
    currentAnswer t h x (some z) =
      some (by classical exact decide (z ∈ core ∨ z = x ∨ ∃ i, h.presentation i = z)) := by
  classical
  simp [currentAnswer]

lemma currentAnswer_false_spec (t : ℕ) (h : Hist t) (x z : ℕ)
    (ha : currentAnswer t h x (some z) = some false) :
    z ∈ ordinary ∧ z ≠ x ∧ ∀ i, h.presentation i ≠ z := by
  classical
  simp [currentAnswer] at ha
  push_neg at ha
  exact ⟨ha.1, ha.2.1, ha.2.2⟩

lemma subset_banIfFreshOrdinary {t : ℕ} (h : Hist t) (x z : ℕ)
    (s : Finset ℕ) : s ⊆ banIfFreshOrdinary h x z s := by
  classical
  intro w hw
  simp only [banIfFreshOrdinary]
  split <;> simp_all

lemma subset_queryBan {t : ℕ} (h : Hist t) (q : Option ℕ) (a : Option Bool) :
    h.forbidden ⊆ queryBan h q a := by
  classical
  intro z hz
  cases q <;> cases a <;> simp [queryBan, hz]
  case some.some b => cases b <;> simp [queryBan, hz]

lemma forbidden_step_mono (gen : FeedbackGenerator) (t : ℕ) (h : Hist t) :
    h.forbidden ⊆ (step gen t h).forbidden := by
  classical
  intro z hz
  simp only [step]
  apply subset_banIfFreshOrdinary _ _ _ _
  exact subset_queryBan h _ _ hz

lemma history_forbidden_mono (gen : FeedbackGenerator) {m n : ℕ} (hmn : m ≤ n) :
    (history gen m).forbidden ⊆ (history gen n).forbidden := by
  induction n, hmn using Nat.le_induction with
  | base => exact fun _ h => h
  | succ n hmn ih =>
      exact fun z hz => forbidden_step_mono gen n (history gen n) (ih hz)


lemma mem_queryBan {t : ℕ} (h : Hist t) (q : Option ℕ) (a : Option Bool) {z : ℕ}
    (hz : z ∈ queryBan h q a) :
    z ∈ h.forbidden ∨ ∃ w, q = some w ∧ a = some false ∧ z = w := by
  classical
  cases q with
  | none => exact Or.inl (by simpa [queryBan] using hz)
  | some w =>
      cases a with
      | none => exact Or.inl (by simpa [queryBan] using hz)
      | some b =>
          cases b with
          | false =>
              have : z = w ∨ z ∈ h.forbidden := by simpa [queryBan] using hz
              rcases this with rfl | hz
              · exact Or.inr ⟨_, rfl, rfl, rfl⟩
              · exact Or.inl hz
          | true => exact Or.inl (by simpa [queryBan] using hz)

lemma mem_nextForbidden {t : ℕ} (h : Hist t) (x : ℕ) (q : Option ℕ)
    (a : Option Bool) (y z : ℕ) (hz : z ∈ nextForbidden h x q a y) :
    z ∈ queryBan h q a ∨
      (y ∈ ordinary ∧ y ≠ x ∧ (∀ i, h.presentation i ≠ y) ∧ z = y) := by
  classical
  by_cases hy : y ∈ ordinary ∧ y ≠ x ∧ ∀ i, h.presentation i ≠ y
  · have : z = y ∨ z ∈ queryBan h q a := by
      simpa [nextForbidden, banIfFreshOrdinary, hy] using hz
    rcases this with rfl | hz
    · exact Or.inr ⟨hy.1, hy.2.1, hy.2.2, rfl⟩
    · exact Or.inl hz
  · exact Or.inl (by simpa [nextForbidden, banIfFreshOrdinary, hy] using hz)

lemma step_forbidden_ordinary (gen : FeedbackGenerator) (t : ℕ) (h : Hist t)
    (hold : ∀ z ∈ h.forbidden, z ∈ ordinary) :
    ∀ z ∈ (step gen t h).forbidden, z ∈ ordinary := by
  classical
  intro z hz
  simp only [step] at hz
  rcases mem_nextForbidden h _ _ _ _ z hz with hq | hy
  · rcases mem_queryBan h _ _ hq with holdz | ⟨w, hqw, haw, hzw⟩
    · exact hold z holdz
    · subst z
      exact (currentAnswer_false_spec t h _ w (by simpa [hqw] using haw)).1
  · simpa [hy.2.2.2] using hy.1

lemma step_forbidden_disjoint (gen : FeedbackGenerator) (t : ℕ) (h : Hist t)
    (hold : ∀ z ∈ h.forbidden, z ∈ ordinary)
    (hdisj : ∀ i, h.presentation i ∉ h.forbidden) :
    ∀ i, (step gen t h).presentation i ∉ (step gen t h).forbidden := by
  classical
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [step, snoc_last]
    intro hz
    rcases mem_nextForbidden h _ _ _ _ _ hz with hq | hy
    · rcases mem_queryBan h _ _ hq with holdz | ⟨w, hqw, haw, hw⟩
      · by_cases ht : Even t
        · have hxcore : nextPresentation t h ∈ core := by
            rw [nextPresentation, if_pos ht]
            exact ⟨t / 2, rfl⟩
          exact (hold _ holdz) hxcore
        · have hx : nextPresentation t h = freshOrd h := by
            simp [nextPresentation, ht]
          rw [hx] at holdz
          exact (freshOrd_not_blocked h) (Finset.mem_union_left _ holdz)
      · have hs := currentAnswer_false_spec t h (nextPresentation t h) w (by simpa [hqw] using haw)
        exact hs.2.1 (by simpa [hw])
    · exact hy.2.1 hy.2.2.2.symm
  · simp only [step, snoc_castSucc]
    intro hz
    rcases mem_nextForbidden h _ _ _ _ _ hz with hq | hy
    · rcases mem_queryBan h _ _ hq with holdz | ⟨w, hqw, haw, hw⟩
      · exact hdisj j holdz
      · have hs := currentAnswer_false_spec t h (nextPresentation t h) w (by simpa [hqw] using haw)
        exact hs.2.2 j (by simpa [hw])
    · exact hy.2.2.1 j (by simpa [hy.2.2.2])

lemma history_good (gen : FeedbackGenerator) (t : ℕ) :
    (∀ z ∈ (history gen t).forbidden, z ∈ ordinary) ∧
    (∀ i, (history gen t).presentation i ∉ (history gen t).forbidden) := by
  induction t with
  | zero => simp [history]
  | succ t ih =>
      exact ⟨step_forbidden_ordinary gen t _ ih.1,
        step_forbidden_disjoint gen t _ ih.1 ih.2⟩


noncomputable def adversarialTarget (gen : FeedbackGenerator) : Language :=
  Set.range (adversarialTranscript gen).presentation

lemma adversarialTarget_mem_class (gen : FeedbackGenerator) :
    adversarialTarget gen ∈ targetClass := by
  let A : Language := adversarialTarget gen \ core
  refine ⟨A, ?_, ?_⟩
  · intro z hz
    exact hz.2
  · apply Set.Subset.antisymm
    · intro z hz
      by_cases hc : z ∈ core
      · exact Or.inl hc
      · exact Or.inr ⟨hz, hc⟩
    · intro z hz
      rcases hz with hc | hA
      · rcases hc with ⟨k, rfl⟩
        exact ⟨2 * k, presentation_core_complete gen k⟩
      · exact hA.1

lemma query_answer_truthful (gen : FeedbackGenerator) (t : ℕ) :
    (adversarialTranscript gen).answer t =
      match (adversarialTranscript gen).query t with
      | none => none
      | some z => some (membershipAnswer (adversarialTarget gen) z) := by
  classical
  rw [transcript_answer_eq, transcript_query_eq]
  cases hq : currentQuery gen t (history gen t)
      (nextPresentation t (history gen t)) with
  | none => simp [currentAnswer, hq]
  | some z =>
      by_cases hp : z ∈ core ∨ z = nextPresentation t (history gen t) ∨
          ∃ i, (history gen t).presentation i = z
      · have hzK : z ∈ adversarialTarget gen := by
          rcases hp with hc | hx | hpast
          · rcases hc with ⟨k, rfl⟩
            exact ⟨2 * k, presentation_core_complete gen k⟩
          · exact ⟨t, by simpa using hx.symm⟩
          · rcases hpast with ⟨i, hi⟩
            exact ⟨i, (transcript_presentation_prefix gen t i).trans hi⟩
        simp [currentAnswer, hq, hp, membershipAnswer, hzK]
      · have hp' : z ∉ core ∧ z ≠ nextPresentation t (history gen t) ∧
            ∀ i, (history gen t).presentation i ≠ z := by
          push_neg at hp
          exact hp
        have hznot : z ∉ adversarialTarget gen := by
          intro hzK
          rcases hzK with ⟨s, hs⟩
          have hst : t < s := by
            apply Nat.lt_of_not_ge
            intro hle
            rcases Nat.lt_or_eq_of_le hle with hlt | heq
            · apply hp'.2.2 ⟨s, hlt⟩
              exact (transcript_presentation_prefix gen t ⟨s, hlt⟩).symm.trans hs
            · subst s
              apply hp'.2.1
              simpa using hs.symm
          have ha : currentAnswer t (history gen t)
              (nextPresentation t (history gen t))
              (currentQuery gen t (history gen t)
                (nextPresentation t (history gen t))) = some false := by
            simp [currentAnswer, hq, hp']
          have ha' : currentAnswer t (history gen t)
              (nextPresentation t (history gen t)) (some z) = some false := by
            simpa [hq] using ha
          have hzforb : z ∈ (history gen (t + 1)).forbidden := by
            simp only [history, step]
            apply subset_banIfFreshOrdinary _ _ _ _
            rw [hq, ha']
            simp [queryBan]
          have hzfuture : z ∈ (history gen (s + 1)).forbidden :=
            history_forbidden_mono gen (Nat.succ_le_succ hst.le) hzforb
          have hpresent : (history gen (s + 1)).presentation (Fin.last s) = z :=
            (transcript_presentation_prefix gen (s + 1) (Fin.last s)).symm.trans hs
          exact (history_good gen (s + 1)).2 (Fin.last s) (hpresent ▸ hzfuture)
        simp [currentAnswer, hq, hp', membershipAnswer, hznot]

lemma adversarial_follows (gen : FeedbackGenerator) :
    FollowsProtocol gen (adversarialTarget gen) (adversarialTranscript gen) := by
  intro t
  have hpref : (fun i : Fin (t + 1) =>
      (adversarialTranscript gen).presentation i) =
      snoc (history gen t).presentation (nextPresentation t (history gen t)) := by
    funext i
    rw [transcript_presentation_prefix gen (t + 1) i]
    rfl
  have haold : (fun i : Fin t => (adversarialTranscript gen).answer i) =
      (history gen t).answer := by
    funext i
    exact transcript_answer_prefix gen t i
  have hanew : (fun i : Fin (t + 1) => (adversarialTranscript gen).answer i) =
      snoc (history gen t).answer
        (currentAnswer t (history gen t) (nextPresentation t (history gen t))
          (currentQuery gen t (history gen t)
            (nextPresentation t (history gen t)))) := by
    funext i
    rw [transcript_answer_prefix gen (t + 1) i]
    rfl
  constructor
  · rw [transcript_query_eq]
    simp only [currentQuery, hpref, haold]
  constructor
  · exact query_answer_truthful gen t
  · rw [transcript_output_eq]
    simp only [currentOutput, hpref, hanew]

lemma adversarial_clean (gen : FeedbackGenerator) :
    Clean (adversarialTranscript gen).presentation (adversarialTarget gen) :=
  fun t => ⟨t, rfl⟩

lemma adversarial_complete (gen : FeedbackGenerator) :
    Complete (adversarialTranscript gen).presentation (adversarialTarget gen) := by
  intro z hz
  exact hz

noncomputable def adversarialPresenter (gen : FeedbackGenerator) : CausalPresenter where
  next t _ _ _ _ := (adversarialTranscript gen).presentation t

lemma adversarial_presented (gen : FeedbackGenerator) :
    PresentedBy (adversarialPresenter gen) (adversarialTranscript gen) := by
  intro t
  rfl

lemma scored_subset_core (gen : FeedbackGenerator) :
    scored (adversarialTarget gen) (adversarialTranscript gen).presentation
      (adversarialTranscript gen).output ⊆ core := by
  classical
  intro z hz
  rcases hz with ⟨hzK, t, hyt, hfresh⟩
  by_contra hzcore
  have hzord : z ∈ ordinary := hzcore
  have hx : z ≠ (adversarialTranscript gen).presentation t := by
    intro heq
    apply hfresh
    exact ⟨t, le_rfl, heq.symm⟩
  have hxnext : z ≠ nextPresentation t (history gen t) := by
    simpa using hx
  have hpast : ∀ i : Fin t, (history gen t).presentation i ≠ z := by
    intro i hi
    apply hfresh
    exact ⟨i, Nat.le_of_lt i.2,
      (transcript_presentation_prefix gen t i).trans hi⟩
  have hzforb : z ∈ (history gen (t + 1)).forbidden := by
    have hban : z ∈ banIfFreshOrdinary (history gen t)
        (nextPresentation t (history gen t)) z
        (queryBan (history gen t)
          (currentQuery gen t (history gen t) (nextPresentation t (history gen t)))
          (currentAnswer t (history gen t) (nextPresentation t (history gen t))
            (currentQuery gen t (history gen t) (nextPresentation t (history gen t))))) := by
      simp [banIfFreshOrdinary, hzord, hxnext, hpast]
    have hy : currentOutput gen t (history gen t)
        (nextPresentation t (history gen t))
        (currentAnswer t (history gen t) (nextPresentation t (history gen t))
          (currentQuery gen t (history gen t) (nextPresentation t (history gen t)))) = z :=
      (transcript_output_eq gen t).symm.trans hyt
    simp only [history, step]
    unfold nextForbidden
    rw [hy]
    exact hban
  rcases hzK with ⟨s, hs⟩
  have hst : t < s := by
    apply Nat.lt_of_not_ge
    intro hle
    exact hfresh ⟨s, hle, hs⟩
  have hzfuture : z ∈ (history gen (s + 1)).forbidden :=
    history_forbidden_mono gen (Nat.succ_le_succ hst.le) hzforb
  have hpresent : (history gen (s + 1)).presentation (Fin.last s) = z :=
    (transcript_presentation_prefix gen (s + 1) (Fin.last s)).symm.trans hs
  exact (history_good gen (s + 1)).2 (Fin.last s) (hpresent ▸ hzfuture)


lemma queryBan_card_le {t : ℕ} (h : Hist t) (q : Option ℕ) (a : Option Bool) :
    (queryBan h q a).card ≤ h.forbidden.card + 1 := by
  classical
  cases q <;> cases a <;> simp [queryBan, Finset.card_insert_le]
  case some.some b => cases b <;> simp [queryBan, Finset.card_insert_le]

lemma banIfFreshOrdinary_card_le {t : ℕ} (h : Hist t) (x z : ℕ) (s : Finset ℕ) :
    (banIfFreshOrdinary h x z s).card ≤ s.card + 1 := by
  classical
  unfold banIfFreshOrdinary
  split <;> simp [Finset.card_insert_le]

lemma nextForbidden_card_le {t : ℕ} (h : Hist t) (x : ℕ) (q : Option ℕ)
    (a : Option Bool) (y : ℕ) :
    (nextForbidden h x q a y).card ≤ h.forbidden.card + 2 := by
  unfold nextForbidden
  exact (banIfFreshOrdinary_card_le h x y _).trans
    (Nat.add_le_add_right (queryBan_card_le h q a) 1)

lemma history_forbidden_card_le (gen : FeedbackGenerator) (t : ℕ) :
    (history gen t).forbidden.card ≤ 2 * t := by
  induction t with
  | zero => simp [history]
  | succ t ih =>
      rw [history_step]
      exact (nextForbidden_card_le (history gen t) _ _ _ _).trans (by omega)

lemma blocked_card_le (gen : FeedbackGenerator) (t : ℕ) :
    (blocked (history gen t)).card ≤ 3 * t := by
  calc
    (blocked (history gen t)).card ≤
        (history gen t).forbidden.card +
          (Finset.univ.image (history gen t).presentation).card :=
      Finset.card_union_le _ _
    _ ≤ (history gen t).forbidden.card + t := by
      gcongr
      simpa using (Finset.card_image_le :
        (Finset.univ.image (history gen t).presentation).card ≤
          (Finset.univ : Finset (Fin t)).card)
    _ ≤ 3 * t := by
      have := history_forbidden_card_le gen t
      omega

lemma freshIndex_le_blocked_card {t : ℕ} (h : Hist t) :
    freshIndex h ≤ (blocked h).card := by
  classical
  let s := (Finset.range (freshIndex h)).image (fun n => 2 * n + 3)
  have hsub : s ⊆ blocked h := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨n, hn, rfl⟩
    have hnlt : n < freshIndex h := Finset.mem_range.mp hn
    exact Classical.byContradiction (Nat.find_min (exists_candidate_not_blocked h) hnlt)
  have hcard : s.card = freshIndex h := by
    rw [show s = (Finset.range (freshIndex h)).image (fun n => 2 * n + 3) by rfl]
    rw [Finset.card_image_iff.mpr]
    · simp
    · intro a _ b _ hab
      exact candidate_injective hab
  rw [← hcard]
  exact Finset.card_le_card hsub

lemma odd_presentation_le (gen : FeedbackGenerator) {t : ℕ} (ht : ¬ Even t) :
    (adversarialTranscript gen).presentation t ≤ 6 * t + 3 := by
  rw [transcript_presentation_eq, nextPresentation, if_neg ht, freshOrd]
  have hfind := freshIndex_le_blocked_card (history gen t)
  have hblocked := blocked_card_le gen t
  omega

lemma odd_presentation_index_le (gen : FeedbackGenerator) (j : ℕ) :
    (adversarialTranscript gen).presentation (2 * j + 1) ≤ 12 * j + 9 := by
  have hodd : ¬ Even (2 * j + 1) := by
    exact Nat.not_even_iff_odd.mpr ⟨j, by omega⟩
  exact (odd_presentation_le gen hodd).trans (by omega)


lemma adversarialTarget_infinite (gen : FeedbackGenerator) :
    (adversarialTarget gen).Infinite := by
  exact Set.infinite_range_of_injective (presentation_injective gen)

noncomputable def orderedAdversarialTarget (gen : FeedbackGenerator) : OrderedLanguage where
  carrier := adversarialTarget gen
  enumeration := Nat.nth (fun z => z ∈ adversarialTarget gen)
  enumeration_injective :=
    (Nat.nth_strictMono (adversarialTarget_infinite gen)).injective
  range_enumeration := Nat.range_nth_of_infinite (adversarialTarget_infinite gen)

lemma orderedAdversarialTarget_strictMono (gen : FeedbackGenerator) :
    InheritsAmbientOrder (orderedAdversarialTarget gen) :=
  Nat.nth_strictMono (adversarialTarget_infinite gen)

noncomputable def targetCount (gen : FeedbackGenerator) (n : ℕ) : ℕ := by
  classical
  exact Nat.count (fun z => z ∈ adversarialTarget gen) n

lemma target_count_lower (gen : FeedbackGenerator) (n : ℕ) :
    n + 1 < targetCount gen (12 * n + 10) + 1 := by
  classical
  unfold targetCount
  rw [Nat.count_eq_card_filter_range]
  let s := (Finset.range (n + 1)).image
    (fun j => (adversarialTranscript gen).presentation (2 * j + 1))
  have hsub : s ⊆ (Finset.range (12 * n + 10)).filter
      (fun z => z ∈ adversarialTarget gen) := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨j, hj, rfl⟩
    have hjlt : j < n + 1 := Finset.mem_range.mp hj
    have hjn : j ≤ n := by omega
    rw [Finset.mem_filter]
    constructor
    · rw [Finset.mem_range]
      exact lt_of_le_of_lt (odd_presentation_index_le gen j) (by omega)
    · exact ⟨2 * j + 1, rfl⟩
  have hcard : s.card = n + 1 := by
    rw [show s = (Finset.range (n + 1)).image
      (fun j => (adversarialTranscript gen).presentation (2 * j + 1)) by rfl]
    rw [Finset.card_image_iff.mpr]
    · simp
    · intro a _ b _ hab
      have := presentation_injective gen hab
      omega
  have hc := Finset.card_le_card hsub
  rw [hcard] at hc
  omega

lemma ordered_enumeration_lt (gen : FeedbackGenerator) (n : ℕ) :
    (orderedAdversarialTarget gen).enumeration n < 12 * n + 10 := by
  classical
  apply Nat.nth_lt_of_lt_count
  have h := target_count_lower gen n
  unfold targetCount at h
  omega

noncomputable def coreExponent (z : ℕ) : ℕ := by
  classical
  exact if hz : z ∈ core then Classical.choose hz else 0

lemma coreExponent_spec {z : ℕ} (hz : z ∈ core) :
    2 ^ coreExponent z = z := by
  classical
  simp [coreExponent, hz, Classical.choose_spec hz]

lemma sq_le_two_pow {k : ℕ} (hk : 4 ≤ k) : k * k ≤ 2 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
      rw [pow_succ]
      have : (k + 1) * (k + 1) ≤ 2 * (k * k) := by nlinarith
      omega

lemma sqrt_linear_bound (n : ℕ) :
    Nat.sqrt (12 * n + 10) < 4 * (Nat.sqrt n + 1) := by
  rw [Nat.sqrt_lt]
  have hs := Nat.lt_succ_sqrt n
  nlinarith

lemma prefixCount_core_le (gen : FeedbackGenerator) (n : ℕ) :
    (orderedAdversarialTarget gen).prefixCount core n ≤
      4 * (Nat.sqrt n + 1) + 4 := by
  classical
  unfold GenLimit.KleinbergWei.OrderedLanguage.prefixCount
  let s := (Finset.range n).filter
    (fun i => (orderedAdversarialTarget gen).enumeration i ∈ core)
  let f := fun i : ℕ => coreExponent ((orderedAdversarialTarget gen).enumeration i)
  have hinj : Set.InjOn f (s : Set ℕ) := by
    intro a ha b hb hab
    have hca : (orderedAdversarialTarget gen).enumeration a ∈ core :=
      (Finset.mem_filter.mp ha).2
    have hcb : (orderedAdversarialTarget gen).enumeration b ∈ core :=
      (Finset.mem_filter.mp hb).2
    apply (orderedAdversarialTarget gen).enumeration_injective
    rw [← coreExponent_spec hca, ← coreExponent_spec hcb]
    change coreExponent ((orderedAdversarialTarget gen).enumeration a) =
      coreExponent ((orderedAdversarialTarget gen).enumeration b) at hab
    rw [hab]
  have hsub : s.image f ⊆ Finset.range (4 * (Nat.sqrt n + 1) + 4) := by
    intro k hk
    rcases Finset.mem_image.mp hk with ⟨i, hi, rfl⟩
    rw [Finset.mem_range]
    have hiN : i < n := (Finset.mem_filter.mp hi).1 |> Finset.mem_range.mp
    have hicore := (Finset.mem_filter.mp hi).2
    have hval : 2 ^ f i < 12 * n + 10 := by
      rw [coreExponent_spec hicore]
      exact (orderedAdversarialTarget_strictMono gen hiN).trans
        (ordered_enumeration_lt gen n)
    by_cases hk4 : 4 ≤ f i
    · have hsq := sq_le_two_pow hk4
      have hle : f i ≤ Nat.sqrt (12 * n + 10) := Nat.le_sqrt.mpr (hsq.trans hval.le)
      have hsqrt := sqrt_linear_bound n
      omega
    · omega
  have hcardImage : (s.image f).card = s.card :=
    Finset.card_image_iff.mpr hinj
  change s.card ≤ _
  rw [← hcardImage]
  exact (Finset.card_le_card hsub).trans (by simp)

lemma ordered_core_upperDensity_zero (gen : FeedbackGenerator) :
    (orderedAdversarialTarget gen).upperDensity core = 0 := by
  have hbound : ∀ n, (orderedAdversarialTarget gen).prefixRatio core n ≤
      4 * (((Nat.sqrt n : ℝ) + 1) / n) + 4 / n := by
    intro n
    by_cases hn : n = 0
    · simp [hn]
    · simp only [GenLimit.KleinbergWei.OrderedLanguage.prefixRatio, hn, if_false]
      have hn0 : (0 : ℝ) ≤ n := by positivity
      have hc : ((orderedAdversarialTarget gen).prefixCount core n : ℝ) ≤
          ((4 * (Nat.sqrt n + 1) + 4 : ℕ) : ℝ) := by
        exact_mod_cast prefixCount_core_le gen n
      apply (div_le_div_of_nonneg_right hc hn0).trans_eq
      push_cast
      ring
  have ht : Tendsto
      (fun n : ℕ => 4 * (((Nat.sqrt n : ℝ) + 1) / n) + 4 / n)
      atTop (nhds 0) := by
    have h1 := GenLimit.InfiniteContamination.tendsto_sparseSqrt_add_one_div
    have h2 : Tendsto (fun n : ℕ => (4 : ℝ) / n) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    simpa using h1.const_mul 4 |>.add h2
  have hratio : Tendsto ((orderedAdversarialTarget gen).prefixRatio core)
      atTop (nhds 0) := by
    apply squeeze_zero (fun n =>
      (orderedAdversarialTarget gen).prefixRatio_nonneg core n) hbound ht
  exact hratio.limsup_eq


lemma scored_upperDensity_zero (gen : FeedbackGenerator) :
    (orderedAdversarialTarget gen).upperDensity
      (scored (adversarialTarget gen) (adversarialTranscript gen).presentation
        (adversarialTranscript gen).output) = 0 := by
  apply le_antisymm
  · exact ((orderedAdversarialTarget gen).upperDensity_mono
      (scored_subset_core gen)).trans_eq (ordered_core_upperDensity_zero gen)
  · exact (orderedAdversarialTarget gen).upperDensity_nonneg _

lemma negative_claim : NegativeClaim := by
  intro gen _
  refine ⟨adversarialTarget gen, adversarialTarget_mem_class gen,
    adversarialPresenter gen, adversarialTranscript gen,
    orderedAdversarialTarget gen, ?_⟩
  exact ⟨rfl, orderedAdversarialTarget_strictMono gen,
    adversarial_presented gen, adversarial_follows gen,
    adversarial_clean gen, presentation_injective gen,
    adversarial_complete gen, scored_upperDensity_zero gen⟩

end Stage3Proof

theorem stage3_result : Stage3S2B.MainClaim := by
  exact ⟨Stage3Proof.targetClass_uncountable,
    Stage3Proof.uniformly_generatable, Stage3Proof.negative_claim⟩
