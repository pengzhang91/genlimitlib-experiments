import Stage3Model
import GenLimit.Paper10_UnionClosednessOfLanguageGeneration.Cardinality
import Mathlib.Data.Set.Enumerate
import Mathlib.Analysis.SpecialFunctions.Log.Base

open Filter

namespace Stage3Work

open Stage3S2B

structure Hist (t : ℕ) where
  x : Fin t → ℕ
  q : Fin t → Option ℕ
  a : Fin t → Option Bool
  y : Fin t → ℕ

def emptyHist : Hist 0 := ⟨Fin.elim0, Fin.elim0, Fin.elim0, Fin.elim0⟩

def extend {t : ℕ} (f : Fin t → α) (v : α) : Fin (t + 1) → α :=
  Fin.lastCases v f

noncomputable def blocked {t : ℕ} (h : Hist t) : Finset ℕ := by
  classical
  exact (Finset.univ.image h.x) ∪
    ((Finset.univ.filter fun i => h.y i ∉ core).image h.y) ∪
    ((Finset.univ.filter fun i =>
      ∃ z, h.q i = some z ∧ z ∉ core ∧ h.a i = some false).image
      (fun i => (h.q i).getD 0))

noncomputable def pick (s : Finset ℕ) : ℕ := by
  classical
  exact Nat.find (p := fun n => n ∉ s) (by
    obtain ⟨n, hn⟩ := Finset.exists_nat_subset_range s
    exact ⟨n, fun hmem => (lt_irrefl n) (by simpa using hn hmem)⟩)

theorem pick_not_mem (s : Finset ℕ) : pick s ∉ s := by
  classical
  exact Nat.find_spec (p := fun n => n ∉ s) (by
    obtain ⟨n, hn⟩ := Finset.exists_nat_subset_range s
    exact ⟨n, fun hmem => (lt_irrefl n) (by simpa using hn hmem)⟩)

noncomputable def step (gen : FeedbackGenerator) {t : ℕ} (h : Hist t) : Hist (t + 1) := by
  classical
  let newX := pick (blocked h)
  let xs := extend h.x newX
  let newQ := gen.query t xs h.a
  let newA := match newQ with
    | none => none
    | some z => some (decide (z ∈ core ∨ ∃ i, xs i = z))
  let answers := extend h.a newA
  let newY := gen.output t xs answers
  exact ⟨xs, extend h.q newQ, answers, extend h.y newY⟩

noncomputable def hist (gen : FeedbackGenerator) : (t : ℕ) → Hist t
  | 0 => emptyHist
  | t + 1 => step gen (hist gen t)

noncomputable def adversarialTranscript (gen : FeedbackGenerator) : Transcript where
  presentation t := (hist gen (t + 1)).x (Fin.last t)
  query t := (hist gen (t + 1)).q (Fin.last t)
  answer t := (hist gen (t + 1)).a (Fin.last t)
  output t := (hist gen (t + 1)).y (Fin.last t)

noncomputable def adversarialTarget (gen : FeedbackGenerator) : Language :=
  core ∪ Set.range (adversarialTranscript gen).presentation

noncomputable def hardcodedPresenter (x : Stream) : CausalPresenter where
  next t _ _ _ _ := x t

end Stage3Work

namespace Stage3Work

open Stage3S2B

@[simp] theorem extend_last {t : ℕ} (f : Fin t → α) (v : α) :
    extend f v (Fin.last t) = v := by simp [extend]

@[simp] theorem extend_castSucc {t : ℕ} (f : Fin t → α) (v : α) (i : Fin t) :
    extend f v i.castSucc = f i := by simp [extend]

@[simp] theorem hist_succ_x_last (gen : FeedbackGenerator) (t : ℕ) :
    (hist gen (t + 1)).x (Fin.last t) = pick (blocked (hist gen t)) := by
  simp [hist, step]

@[simp] theorem hist_succ_q_last (gen : FeedbackGenerator) (t : ℕ) :
    (hist gen (t + 1)).q (Fin.last t) =
      gen.query t (extend (hist gen t).x (pick (blocked (hist gen t)))) (hist gen t).a := by
  simp [hist, step]

@[simp] theorem hist_succ_x_castSucc (gen : FeedbackGenerator) {t : ℕ} (i : Fin t) :
    (hist gen (t + 1)).x i.castSucc = (hist gen t).x i := by
  simp [hist, step]

@[simp] theorem hist_succ_q_castSucc (gen : FeedbackGenerator) {t : ℕ} (i : Fin t) :
    (hist gen (t + 1)).q i.castSucc = (hist gen t).q i := by
  simp [hist, step]

@[simp] theorem hist_succ_a_castSucc (gen : FeedbackGenerator) {t : ℕ} (i : Fin t) :
    (hist gen (t + 1)).a i.castSucc = (hist gen t).a i := by
  simp [hist, step]

@[simp] theorem hist_succ_y_castSucc (gen : FeedbackGenerator) {t : ℕ} (i : Fin t) :
    (hist gen (t + 1)).y i.castSucc = (hist gen t).y i := by
  simp [hist, step]

end Stage3Work

namespace Stage3Work

open Stage3S2B

 theorem hist_x_mono (gen : FeedbackGenerator) {s t : ℕ} (hst : s ≤ t) (i : Fin s) :
    (hist gen t).x (Fin.castLE hst i) = (hist gen s).x i := by
  induction t, hst using Nat.le_induction with
  | base => rfl
  | succ t hst ih =>
      rw [show Fin.castLE (Nat.le.step hst) i = (Fin.castLE hst i).castSucc by rfl]
      simpa using (hist_succ_x_castSucc gen (Fin.castLE hst i)).trans ih

 theorem hist_q_mono (gen : FeedbackGenerator) {s t : ℕ} (hst : s ≤ t) (i : Fin s) :
    (hist gen t).q (Fin.castLE hst i) = (hist gen s).q i := by
  induction t, hst using Nat.le_induction with
  | base => rfl
  | succ t hst ih =>
      rw [show Fin.castLE (Nat.le.step hst) i = (Fin.castLE hst i).castSucc by rfl]
      simpa using (hist_succ_q_castSucc gen (Fin.castLE hst i)).trans ih

 theorem hist_a_mono (gen : FeedbackGenerator) {s t : ℕ} (hst : s ≤ t) (i : Fin s) :
    (hist gen t).a (Fin.castLE hst i) = (hist gen s).a i := by
  induction t, hst using Nat.le_induction with
  | base => rfl
  | succ t hst ih =>
      rw [show Fin.castLE (Nat.le.step hst) i = (Fin.castLE hst i).castSucc by rfl]
      simpa using (hist_succ_a_castSucc gen (Fin.castLE hst i)).trans ih

 theorem hist_y_mono (gen : FeedbackGenerator) {s t : ℕ} (hst : s ≤ t) (i : Fin s) :
    (hist gen t).y (Fin.castLE hst i) = (hist gen s).y i := by
  induction t, hst using Nat.le_induction with
  | base => rfl
  | succ t hst ih =>
      rw [show Fin.castLE (Nat.le.step hst) i = (Fin.castLE hst i).castSucc by rfl]
      simpa using (hist_succ_y_castSucc gen (Fin.castLE hst i)).trans ih

 theorem transcript_x_eq_hist (gen : FeedbackGenerator) {t : ℕ} (i : Fin t) :
    (adversarialTranscript gen).presentation i = (hist gen t).x i := by
  let j : Fin (i.val + 1) := Fin.last i.val
  have hle : i.val + 1 ≤ t := i.isLt
  have hm := hist_x_mono gen hle j
  have hcast : Fin.castLE hle j = i := by apply Fin.ext; simp [j]
  simpa [adversarialTranscript, j, hcast] using hm.symm

 theorem transcript_q_eq_hist (gen : FeedbackGenerator) {t : ℕ} (i : Fin t) :
    (adversarialTranscript gen).query i = (hist gen t).q i := by
  let j : Fin (i.val + 1) := Fin.last i.val
  have hle : i.val + 1 ≤ t := i.isLt
  have hm := hist_q_mono gen hle j
  have hcast : Fin.castLE hle j = i := by apply Fin.ext; simp [j]
  simpa [adversarialTranscript, j, hcast] using hm.symm

 theorem transcript_a_eq_hist (gen : FeedbackGenerator) {t : ℕ} (i : Fin t) :
    (adversarialTranscript gen).answer i = (hist gen t).a i := by
  let j : Fin (i.val + 1) := Fin.last i.val
  have hle : i.val + 1 ≤ t := i.isLt
  have hm := hist_a_mono gen hle j
  have hcast : Fin.castLE hle j = i := by apply Fin.ext; simp [j]
  simpa [adversarialTranscript, j, hcast] using hm.symm

 theorem transcript_y_eq_hist (gen : FeedbackGenerator) {t : ℕ} (i : Fin t) :
    (adversarialTranscript gen).output i = (hist gen t).y i := by
  let j : Fin (i.val + 1) := Fin.last i.val
  have hle : i.val + 1 ≤ t := i.isLt
  have hm := hist_y_mono gen hle j
  have hcast : Fin.castLE hle j = i := by apply Fin.ext; simp [j]
  simpa [adversarialTranscript, j, hcast] using hm.symm

end Stage3Work

namespace Stage3Work

open Stage3S2B

lemma presentation_eq_pick (gen : FeedbackGenerator) (t : ℕ) :
    (adversarialTranscript gen).presentation t = pick (blocked (hist gen t)) := by
  simp [adversarialTranscript]

lemma prior_x_mem_blocked (gen : FeedbackGenerator) {s t : ℕ} (hst : s < t) :
    (adversarialTranscript gen).presentation s ∈ blocked (hist gen t) := by
  classical
  have hs : s < t := hst
  let i : Fin t := ⟨s, hs⟩
  have hi : (hist gen t).x i = (adversarialTranscript gen).presentation s := by
    symm
    simpa [i] using transcript_x_eq_hist gen i
  simp [blocked, ← hi, i]

lemma presentation_injective (gen : FeedbackGenerator) :
    Function.Injective (adversarialTranscript gen).presentation := by
  intro s t hst
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have hmem := prior_x_mem_blocked gen hlt
    rw [hst, presentation_eq_pick gen t] at hmem
    exact pick_not_mem _ hmem
  · have hmem := prior_x_mem_blocked gen hlt
    rw [← hst, presentation_eq_pick gen s] at hmem
    exact pick_not_mem _ hmem

lemma prior_ordinary_output_mem_blocked (gen : FeedbackGenerator) {s t z : ℕ}
    (hst : s < t) (hy : (adversarialTranscript gen).output s = z)
    (hz : z ∉ core) : z ∈ blocked (hist gen t) := by
  classical
  let i : Fin t := ⟨s, hst⟩
  have hiy : (hist gen t).y i = z := by
    rw [← hy]
    symm
    simpa [i] using transcript_y_eq_hist gen i
  unfold blocked
  apply Finset.mem_union_left _
  apply Finset.mem_union_right
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨i, by simpa [hiy] using hz, hiy⟩

lemma fresh_ordinary_output_not_range (gen : FeedbackGenerator) {t z : ℕ}
    (hy : (adversarialTranscript gen).output t = z)
    (hz : z ∉ core)
    (hfresh : z ∉ observedThrough (adversarialTranscript gen).presentation t) :
    z ∉ Set.range (adversarialTranscript gen).presentation := by
  rintro ⟨s, hs⟩
  by_cases hst : s ≤ t
  · apply hfresh
    exact ⟨s, hst, hs⟩
  · have hlt : t < s := Nat.lt_of_not_ge hst
    have hmem := prior_ordinary_output_mem_blocked gen hlt hy hz
    rw [← hs, presentation_eq_pick gen s] at hmem
    exact pick_not_mem _ hmem

lemma scored_subset_core (gen : FeedbackGenerator) :
    scored (adversarialTarget gen) (adversarialTranscript gen).presentation
      (adversarialTranscript gen).output ⊆ core := by
  rintro z ⟨hzK, t, hyt, hfresh⟩
  by_contra hzcore
  have hnrange := fresh_ordinary_output_not_range gen hyt hzcore hfresh
  exact hnrange (hzK.resolve_left hzcore)

lemma target_mem_class (gen : FeedbackGenerator) : adversarialTarget gen ∈ targetClass := by
  refine ⟨Set.range (adversarialTranscript gen).presentation \ core, ?_, ?_⟩
  · intro z hz
    exact hz.2
  · ext z
    simp [adversarialTarget]

lemma transcript_clean (gen : FeedbackGenerator) :
    Clean (adversarialTranscript gen).presentation (adversarialTarget gen) := by
  intro t
  exact Or.inr ⟨t, rfl⟩

end Stage3Work
