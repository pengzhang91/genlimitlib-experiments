import Stage3Model
import Mathlib.Analysis.SpecialFunctions.Log.Base

open Set Filter

namespace Stage3Proof

open Stage3S2B

noncomputable def mex (s : Finset ℕ) : ℕ := Nat.find s.exists_not_mem

theorem mex_not_mem (s : Finset ℕ) : mex s ∉ s := Nat.find_spec s.exists_not_mem

theorem lt_mex_mem (s : Finset ℕ) {n : ℕ} (h : n < mex s) : n ∈ s := by
  exact Classical.not_not.mp (Nat.find_min s.exists_notMem h)

theorem mex_le_card (s : Finset ℕ) : mex s ≤ s.card := by
  have hsub : Finset.range (mex s) ⊆ s := by
    intro n hn
    exact lt_mex_mem s (Finset.mem_range.mp hn)
  simpa using Finset.card_le_card hsub

def snoc {α : Type*} {t : ℕ} (f : Fin t → α) (a : α) : Fin (t + 1) → α :=
  Fin.lastCases a f

@[simp] theorem snoc_last {α : Type*} {t : ℕ} (f : Fin t → α) (a : α) :
    snoc f a (Fin.last t) = a := by simp [snoc]

@[simp] theorem snoc_castSucc {α : Type*} {t : ℕ} (f : Fin t → α) (a : α) (i : Fin t) :
    snoc f a i.castSucc = f i := by simp [snoc]

structure State (gen : FeedbackGenerator) (t : ℕ) where
  presentation : Fin t → ℕ
  query : Fin t → Option ℕ
  answer : Fin t → Option Bool
  output : Fin t → ℕ
  rejected : Finset ℕ

def State.presented {gen : FeedbackGenerator} {t : ℕ} (s : State gen t) : Finset ℕ :=
  Finset.univ.image s.presentation

noncomputable def step {gen : FeedbackGenerator} {t : ℕ} (s : State gen t) : State gen (t + 1) := by
  classical
  let x := mex (s.presented ∪ s.rejected)
  let pres := snoc s.presentation x
  let q := gen.query t pres s.answer
  let admitted := insert x s.presented
  let a : Option Bool := q.map fun z => decide (z ∈ core ∨ z ∈ admitted)
  let rq := match q with
    | none => s.rejected
    | some z => if z ∈ core ∨ z ∈ admitted then s.rejected else insert z s.rejected
  let y := gen.output t pres (snoc s.answer a)
  let rnext := if y ∈ core ∨ y ∈ admitted then rq else insert y rq
  exact {
    presentation := pres
    query := snoc s.query q
    answer := snoc s.answer a
    output := snoc s.output y
    rejected := rnext
  }

noncomputable def states (gen : FeedbackGenerator) : (t : ℕ) → State gen t
  | 0 => {
      presentation := Fin.elim0
      query := Fin.elim0
      answer := Fin.elim0
      output := Fin.elim0
      rejected := ∅
    }
  | t + 1 => step (states gen t)

noncomputable def x (gen : FeedbackGenerator) (t : ℕ) : ℕ :=
  mex ((states gen t).presented ∪ (states gen t).rejected)

noncomputable def q (gen : FeedbackGenerator) (t : ℕ) : Option ℕ :=
  gen.query t (snoc (states gen t).presentation (x gen t)) (states gen t).answer

noncomputable def admitted (gen : FeedbackGenerator) (t : ℕ) : Finset ℕ :=
  insert (x gen t) (states gen t).presented

noncomputable def a (gen : FeedbackGenerator) (t : ℕ) : Option Bool := by
  classical
  exact (q gen t).map fun z => decide (z ∈ core ∨ z ∈ admitted gen t)

noncomputable def y (gen : FeedbackGenerator) (t : ℕ) : ℕ :=
  gen.output t (snoc (states gen t).presentation (x gen t))
    (snoc (states gen t).answer (a gen t))

noncomputable def K (gen : FeedbackGenerator) : Language := core ∪ Set.range (x gen)

noncomputable def tr (gen : FeedbackGenerator) : Transcript := {
  presentation := x gen
  query := q gen
  answer := a gen
  output := y gen
}

noncomputable def presenter (gen : FeedbackGenerator) : CausalPresenter := {
  next := fun t _ _ _ _ => x gen t
}

@[simp] theorem states_succ_presentation_last (gen : FeedbackGenerator) (t : ℕ) :
    (states gen (t + 1)).presentation (Fin.last t) = x gen t := by
  simp [states, step, x]

@[simp] theorem states_succ_query_last (gen : FeedbackGenerator) (t : ℕ) :
    (states gen (t + 1)).query (Fin.last t) = q gen t := by
  simp [states, step, q, x]

@[simp] theorem states_succ_answer_last (gen : FeedbackGenerator) (t : ℕ) :
    (states gen (t + 1)).answer (Fin.last t) = a gen t := by
  classical
  simp [states, step, a, q, admitted, x]

@[simp] theorem states_succ_output_last (gen : FeedbackGenerator) (t : ℕ) :
    (states gen (t + 1)).output (Fin.last t) = y gen t := by
  classical
  simp [states, step, y, a, q, admitted, x]

@[simp] theorem states_succ_presentation_castSucc (gen : FeedbackGenerator) (t : ℕ) (i : Fin t) :
    (states gen (t + 1)).presentation i.castSucc = (states gen t).presentation i := by
  simp [states, step]

@[simp] theorem states_succ_query_castSucc (gen : FeedbackGenerator) (t : ℕ) (i : Fin t) :
    (states gen (t + 1)).query i.castSucc = (states gen t).query i := by
  simp [states, step]

@[simp] theorem states_succ_answer_castSucc (gen : FeedbackGenerator) (t : ℕ) (i : Fin t) :
    (states gen (t + 1)).answer i.castSucc = (states gen t).answer i := by
  simp [states, step]

@[simp] theorem states_succ_output_castSucc (gen : FeedbackGenerator) (t : ℕ) (i : Fin t) :
    (states gen (t + 1)).output i.castSucc = (states gen t).output i := by
  simp [states, step]

theorem state_presentation_eq (gen : FeedbackGenerator) {t : ℕ} (i : Fin t) :
    (states gen t).presentation i = x gen i := by
  induction t with
  | zero => exact Fin.elim0 i
  | succ t ih =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · exact states_succ_presentation_last gen t
      · simpa using ih j

theorem state_query_eq (gen : FeedbackGenerator) {t : ℕ} (i : Fin t) :
    (states gen t).query i = q gen i := by
  induction t with
  | zero => exact Fin.elim0 i
  | succ t ih =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · exact states_succ_query_last gen t
      · simpa using ih j

theorem state_answer_eq (gen : FeedbackGenerator) {t : ℕ} (i : Fin t) :
    (states gen t).answer i = a gen i := by
  induction t with
  | zero => exact Fin.elim0 i
  | succ t ih =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · exact states_succ_answer_last gen t
      · simpa using ih j

theorem state_output_eq (gen : FeedbackGenerator) {t : ℕ} (i : Fin t) :
    (states gen t).output i = y gen i := by
  induction t with
  | zero => exact Fin.elim0 i
  | succ t ih =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · exact states_succ_output_last gen t
      · simpa using ih j

theorem step_presented {gen : FeedbackGenerator} {t : ℕ} (s : State gen t) :
    (step s).presented = insert (mex (s.presented ∪ s.rejected)) s.presented := by
  classical
  ext z
  simp only [State.presented, step, Finset.mem_image, Finset.mem_univ, true_and,
    Finset.mem_insert]
  constructor
  · rintro ⟨i, rfl⟩
    refine Fin.lastCases ?_ (fun j => ?_) i
    · exact Or.inl (by simp)
    · exact Or.inr ⟨j, by simp⟩
  · rintro (rfl | ⟨i, rfl⟩)
    · exact ⟨Fin.last t, by simp⟩
    · exact ⟨i.castSucc, by simp⟩

theorem step_rejected_mono {gen : FeedbackGenerator} {t : ℕ} (s : State gen t) :
    s.rejected ⊆ (step s).rejected := by
  classical
  intro z hz
  unfold step
  dsimp
  generalize gen.query t (snoc s.presentation (mex (s.presented ∪ s.rejected))) s.answer = qq
  cases qq with
  | none => split <;> simp_all
  | some queryPoint =>
      by_cases hquery : queryPoint ∈ core ∨
          queryPoint ∈ insert (mex (s.presented ∪ s.rejected)) s.presented
      · simp only [if_pos hquery]
        split <;> simp_all
      · simp only [if_neg hquery]
        split <;> simp_all

theorem step_rejected_card {gen : FeedbackGenerator} {t : ℕ} (s : State gen t) :
    (step s).rejected.card ≤ s.rejected.card + 2 := by
  classical
  unfold step
  dsimp
  generalize hq : gen.query t
    (snoc s.presentation (mex (s.presented ∪ s.rejected))) s.answer = qq
  cases qq with
  | none =>
      simp only [hq]
      split
      · omega
      · exact (Finset.card_insert_le _ _).trans (by omega)
  | some queryPoint =>
      simp only [hq]
      by_cases hquery : queryPoint ∈ core ∨
          queryPoint ∈ insert (mex (s.presented ∪ s.rejected)) s.presented
      · simp only [if_pos hquery]
        split
        · omega
        · exact (Finset.card_insert_le _ _).trans (by omega)
      · simp only [if_neg hquery]
        split
        · exact (Finset.card_insert_le _ _).trans (by omega)
        · calc
            (insert _ (insert queryPoint s.rejected)).card ≤
                (insert queryPoint s.rejected).card + 1 := Finset.card_insert_le _ _
            _ ≤ s.rejected.card + 2 := by
              have := Finset.card_insert_le queryPoint s.rejected
              omega

theorem step_used_mono {gen : FeedbackGenerator} {t : ℕ} (s : State gen t) :
    s.presented ∪ s.rejected ⊆ (step s).presented ∪ (step s).rejected := by
  intro z hz
  rcases Finset.mem_union.mp hz with hz | hz
  · apply Finset.mem_union_left
    rw [step_presented]
    exact Finset.mem_insert_of_mem hz
  · exact Finset.mem_union_right _ (step_rejected_mono s hz)

theorem step_mex_lt {gen : FeedbackGenerator} {t : ℕ} (s : State gen t) :
    mex (s.presented ∪ s.rejected) < mex ((step s).presented ∪ (step s).rejected) := by
  let oldUsed := s.presented ∪ s.rejected
  let newUsed := (step s).presented ∪ (step s).rejected
  have hnew : mex newUsed ∉ newUsed := mex_not_mem newUsed
  have holdsub : oldUsed ⊆ newUsed := step_used_mono s
  have hcurrent : mex oldUsed ∈ newUsed := by
    apply Finset.mem_union_left
    rw [step_presented]
    exact Finset.mem_insert_self _ _
  by_contra hnot
  have hle : mex newUsed ≤ mex oldUsed := Nat.le_of_not_gt hnot
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact hnew (holdsub (lt_mex_mem oldUsed hlt))
  · exact hnew (heq ▸ hcurrent)

theorem x_strictMono (gen : FeedbackGenerator) : StrictMono (x gen) := by
  apply strictMono_nat_of_lt_succ
  intro t
  rw [x, x, states]
  exact step_mex_lt (states gen t)

theorem x_injective (gen : FeedbackGenerator) : Function.Injective (x gen) :=
  (x_strictMono gen).injective

theorem step_rejected_ordinary {gen : FeedbackGenerator} {t : ℕ} (s : State gen t)
    (h : ∀ z ∈ s.rejected, z ∈ ordinary) :
    ∀ z ∈ (step s).rejected, z ∈ ordinary := by
  classical
  unfold step
  dsimp
  generalize gen.query t (snoc s.presentation (mex (s.presented ∪ s.rejected))) s.answer = qq
  cases qq with
  | none =>
      dsimp
      split <;> simp_all [ordinary]
  | some queryPoint =>
      dsimp
      by_cases hquery : queryPoint ∈ core ∨
          queryPoint ∈ insert (mex (s.presented ∪ s.rejected)) s.presented
      · simp only [if_pos hquery]
        split <;> simp_all [ordinary]
      · simp only [if_neg hquery]
        split <;> simp_all [ordinary]

theorem rejected_ordinary (gen : FeedbackGenerator) (t : ℕ) :
    ∀ z ∈ (states gen t).rejected, z ∈ ordinary := by
  induction t with
  | zero => simp [states]
  | succ t ih =>
      simpa [states] using step_rejected_ordinary (states gen t) ih

theorem rejected_mono_succ (gen : FeedbackGenerator) (t : ℕ) :
    (states gen t).rejected ⊆ (states gen (t + 1)).rejected := by
  simpa [states] using step_rejected_mono (states gen t)

theorem rejected_mono_of_le (gen : FeedbackGenerator) {t u : ℕ} (htu : t ≤ u) :
    (states gen t).rejected ⊆ (states gen u).rejected := by
  induction u, htu using Nat.le_induction with
  | base => exact fun _ h => h
  | succ u htu ih => exact fun z hz => rejected_mono_succ gen u (ih hz)

theorem x_not_rejected (gen : FeedbackGenerator) (t : ℕ) :
    x gen t ∉ (states gen t).rejected := by
  intro h
  exact mex_not_mem ((states gen t).presented ∪ (states gen t).rejected)
    (Finset.mem_union_right _ h)

theorem rejected_not_future_x (gen : FeedbackGenerator) {t u z : ℕ}
    (hz : z ∈ (states gen t).rejected) (htu : t ≤ u) : z ≠ x gen u := by
  intro heq
  subst z
  exact x_not_rejected gen u (rejected_mono_of_le gen htu hz)

theorem core_subset_range_x (gen : FeedbackGenerator) : core ⊆ Set.range (x gen) := by
  intro z hz
  let t := z + 1
  have hzt : z < x gen t := by
    have hid := (x_strictMono gen).id_le t
    dsimp [t] at hid ⊢
    omega
  have hused : z ∈ (states gen t).presented ∪ (states gen t).rejected := by
    exact lt_mex_mem _ (by simpa [x] using hzt)
  rcases Finset.mem_union.mp hused with hp | hr
  · rw [State.presented] at hp
    rcases Finset.mem_image.mp hp with ⟨i, _, hi⟩
    exact ⟨i, by simpa [state_presentation_eq] using hi⟩
  · exact False.elim ((rejected_ordinary gen t z hr) hz)

theorem range_x_eq_K (gen : FeedbackGenerator) : Set.range (x gen) = K gen := by
  apply Set.Subset.antisymm
  · intro z hz
    exact Or.inr hz
  · intro z hz
    rcases hz with hz | hz
    · exact core_subset_range_x gen hz
    · exact hz

theorem K_targetClass (gen : FeedbackGenerator) : K gen ∈ targetClass := by
  refine ⟨Set.range (x gen) \ core, ?_, ?_⟩
  · intro z hz
    exact hz.2
  · ext z
    simp only [K, Set.mem_union, Set.mem_diff, Set.mem_range]
    tauto

theorem clean_x (gen : FeedbackGenerator) : Clean (x gen) (K gen) := by
  intro t
  exact Or.inr ⟨t, rfl⟩

theorem complete_x (gen : FeedbackGenerator) : Complete (x gen) (K gen) := by
  intro z hz
  rw [← range_x_eq_K gen] at hz
  exact hz

theorem rejected_card (gen : FeedbackGenerator) (t : ℕ) :
    (states gen t).rejected.card ≤ 2 * t := by
  induction t with
  | zero => simp [states]
  | succ t ih =>
      rw [states]
      have hs := step_rejected_card (states gen t)
      omega

theorem presented_card_le (gen : FeedbackGenerator) (t : ℕ) :
    (states gen t).presented.card ≤ t := by
  exact (Finset.card_image_le.trans_eq (Finset.card_univ.trans (Fintype.card_fin t)))

theorem x_le_three_mul (gen : FeedbackGenerator) (t : ℕ) : x gen t ≤ 3 * t := by
  rw [x]
  calc
    mex ((states gen t).presented ∪ (states gen t).rejected) ≤
        ((states gen t).presented ∪ (states gen t).rejected).card := mex_le_card _
    _ ≤ (states gen t).presented.card + (states gen t).rejected.card :=
      Finset.card_union_le _ _
    _ ≤ t + 2 * t := Nat.add_le_add (presented_card_le gen t) (rejected_card gen t)
    _ = 3 * t := by omega

theorem mem_admitted_iff (gen : FeedbackGenerator) (t z : ℕ) :
    z ∈ admitted gen t ↔ ∃ i : Fin (t + 1), x gen i = z := by
  classical
  constructor
  · intro hz
    rw [admitted, Finset.mem_insert] at hz
    rcases hz with rfl | hz
    · exact ⟨Fin.last t, rfl⟩
    · rw [State.presented] at hz
      rcases Finset.mem_image.mp hz with ⟨i, _, hi⟩
      exact ⟨i.castSucc, by simpa [state_presentation_eq] using hi⟩
  · rintro ⟨i, rfl⟩
    refine Fin.lastCases ?_ (fun j => ?_) i
    · exact Finset.mem_insert_self _ _
    · rw [admitted, Finset.mem_insert]
      exact Or.inr (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, state_presentation_eq gen j⟩)

theorem query_false_rejected (gen : FeedbackGenerator) (t z : ℕ)
    (hqz : q gen t = some z) (hz : z ∉ core ∧ z ∉ admitted gen t) :
    z ∈ (states gen (t + 1)).rejected := by
  classical
  rw [states]
  unfold step
  dsimp
  have hquery : gen.query t
      (snoc (states gen t).presentation (mex ((states gen t).presented ∪ (states gen t).rejected)))
      (states gen t).answer = some z := by
    simpa [q, x] using hqz
  have hinsert : z ∉ insert
      (mex ((states gen t).presented ∪ (states gen t).rejected))
      (states gen t).presented := by
    intro h
    apply hz.2
    simpa [admitted, x] using h
  rw [hquery]
  simp only [hz.1, false_or]
  rw [if_neg hinsert]
  split <;> simp

theorem output_fresh_ordinary_rejected (gen : FeedbackGenerator) (t : ℕ)
    (hy : y gen t ∉ core ∧ y gen t ∉ admitted gen t) :
    y gen t ∈ (states gen (t + 1)).rejected := by
  classical
  rw [states]
  unfold step
  dsimp
  have hout : gen.output t
      (snoc (states gen t).presentation (mex ((states gen t).presented ∪ (states gen t).rejected)))
      (snoc (states gen t).answer
        (Option.map (fun z => decide (z ∈ core ∨ z ∈ insert
          (mex ((states gen t).presented ∪ (states gen t).rejected)) (states gen t).presented))
          (gen.query t (snoc (states gen t).presentation
            (mex ((states gen t).presented ∪ (states gen t).rejected)))
            (states gen t).answer))) = y gen t := by
    simp [y, a, q, admitted, x]
  rw [hout]
  have hadmitted : insert (mex ((states gen t).presented ∪ (states gen t).rejected))
      (states gen t).presented = admitted gen t := by simp [admitted, x]
  rw [hadmitted]
  simp only [hy, or_false, false_or, if_false, Finset.mem_insert, true_or]

theorem rejected_after_not_range (gen : FeedbackGenerator) (t z : ℕ)
    (hpast : z ∉ admitted gen t) (hr : z ∈ (states gen (t + 1)).rejected) :
    z ∉ Set.range (x gen) := by
  rintro ⟨u, hu⟩
  by_cases hut : u ≤ t
  · apply hpast
    rw [mem_admitted_iff]
    exact ⟨⟨u, by omega⟩, hu⟩
  · have htu : t + 1 ≤ u := by omega
    exact rejected_not_future_x gen hr htu hu.symm

theorem answer_truth (gen : FeedbackGenerator) (t : ℕ) :
    a gen t = match q gen t with
      | none => none
      | some z => some (membershipAnswer (K gen) z) := by
  classical
  rw [a]
  cases hq : q gen t with
  | none => simp [hq]
  | some z =>
      simp only [hq, Option.map_some]
      congr 1
      change decide (z ∈ core ∨ z ∈ admitted gen t) = decide (z ∈ K gen)
      congr 1
      apply propext
      constructor
      · intro hz
        rcases hz with hz | hz
        · exact Or.inl hz
        · rw [mem_admitted_iff] at hz
          rcases hz with ⟨i, hi⟩
          exact Or.inr ⟨i, hi⟩
      · intro hzK
        rcases hzK with hzcore | hzrange
        · exact Or.inl hzcore
        · by_contra hnot
          have hznot : z ∉ core ∧ z ∉ admitted gen t := by tauto
          have hr := query_false_rejected gen t z hq hznot
          exact rejected_after_not_range gen t z hznot.2 hr hzrange

theorem follows (gen : FeedbackGenerator) : FollowsProtocol gen (K gen) (tr gen) := by
  intro t
  constructor
  · change q gen t = gen.query t (fun i => x gen i) (fun i => a gen i)
    rw [q]
    congr 1
    · funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp
      · simp [state_presentation_eq]
    · funext i
      simp [state_answer_eq]
  constructor
  · exact answer_truth gen t
  · change y gen t = gen.output t (fun i => x gen i) (fun i => a gen i)
    rw [y]
    congr 1
    · funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp
      · simp [state_presentation_eq]
    · funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp
      · simp [state_answer_eq]

theorem presented (gen : FeedbackGenerator) : PresentedBy (presenter gen) (tr gen) := by
  intro t
  rfl

theorem scored_subset_core (gen : FeedbackGenerator) :
    scored (K gen) (x gen) (y gen) ⊆ core := by
  intro z hz
  rcases hz with ⟨hzK, t, hyt, hfresh⟩
  by_contra hzcore
  have hpast : z ∉ admitted gen t := by
    intro ha
    rw [mem_admitted_iff] at ha
    rcases ha with ⟨i, hi⟩
    apply hfresh
    exact ⟨i, Nat.le_of_lt_succ i.isLt, by simpa [hyt] using hi⟩
  have hyordinary : y gen t ∉ core ∧ y gen t ∉ admitted gen t := by
    simpa [hyt] using And.intro hzcore hpast
  have hr := output_fresh_ordinary_rejected gen t hyordinary
  have hnrange := rejected_after_not_range gen t z hpast (by simpa [hyt] using hr)
  exact hnrange ((range_x_eq_K gen).symm ▸ hzK)

noncomputable def orderedK (gen : FeedbackGenerator) : OrderedLanguage := {
  carrier := K gen
  enumeration := x gen
  enumeration_injective := x_injective gen
  range_enumeration := range_x_eq_K gen
}

theorem orderedK_inherits (gen : FeedbackGenerator) : InheritsAmbientOrder (orderedK gen) :=
  x_strictMono gen

 theorem core_prefixCount_le_log (gen : FeedbackGenerator) (n : ℕ) :
    (orderedK gen).prefixCount core n ≤ Nat.log 2 (3 * n) + 1 := by
  classical
  let indices := (Finset.range n).filter fun i => x gen i ∈ core
  let values := indices.image (x gen)
  let powers := (Finset.range (Nat.log 2 (3 * n) + 1)).image fun k => 2 ^ k
  have hcard : indices.card = values.card := by
    apply (Finset.card_image_iff.mpr ?_).symm
    intro i hi j hj hij
    exact x_injective gen hij
  have hsub : values ⊆ powers := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨i, hi, rfl⟩
    have hirange : i < n := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
    have hicore : x gen i ∈ core := (Finset.mem_filter.mp hi).2
    rcases hicore with ⟨k, hk⟩
    have hn : 3 * n ≠ 0 := by omega
    change 2 ^ k = x gen i at hk
    have hpow : 2 ^ k ≤ 3 * n := by
      rw [hk]
      exact (x_le_three_mul gen i).trans (by omega)
    have hklog : k ≤ Nat.log 2 (3 * n) :=
      (Nat.pow_le_iff_le_log (by omega) hn).mp hpow
    apply Finset.mem_image.mpr
    exact ⟨k, Finset.mem_range.mpr (by omega), hk⟩
  change indices.card ≤ Nat.log 2 (3 * n) + 1
  rw [hcard]
  have hpcard : powers.card ≤ Nat.log 2 (3 * n) + 1 := by
    simpa [powers] using (Finset.card_image_le :
      ((Finset.range (Nat.log 2 (3 * n) + 1)).image fun k => 2 ^ k).card ≤
        (Finset.range (Nat.log 2 (3 * n) + 1)).card)
  exact (Finset.card_le_card hsub).trans hpcard

 theorem log_ratio_tendsto_zero :
    Tendsto (fun n : ℕ => ((Nat.log 2 (3 * n) + 1 : ℕ) : ℝ) / n) atTop (nhds 0) := by
  have harg : Tendsto (fun n : ℕ => (3 * n : ℝ)) atTop atTop := by
    simpa [Nat.cast_mul] using
      (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num : (0 : ℝ) < 3))
  have hlog : Tendsto (fun n : ℕ => Real.logb 2 (3 * n : ℝ) / n) atTop (nhds 0) := by
    have h := (Real.tendsto_pow_logb_div_mul_add_atTop (b := 2) (1 / 3) 0 1
      (by norm_num : (1 / 3 : ℝ) ≠ 0)).comp harg
    convert h using 1
    ext n
    simp [div_eq_mul_inv]
  have hone : Tendsto (fun n : ℕ => (1 : ℝ) / n) atTop (nhds 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  apply squeeze_zero' (g := fun n : ℕ => Real.logb 2 (3 * n : ℝ) / n + 1 / n)
  · filter_upwards with n
    positivity
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hnat := Real.natLog_le_logb (3 * n) 2
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    have hnat' : (Nat.log 2 (3 * n) : ℝ) ≤ Real.logb 2 (3 * n : ℝ) := by
      simpa [Nat.cast_mul] using hnat
    rw [Nat.cast_add, Nat.cast_one, add_div]
    gcongr
  · simpa using hlog.add hone

 theorem core_prefixRatio_tendsto_zero (gen : FeedbackGenerator) :
    Tendsto ((orderedK gen).prefixRatio core) atTop (nhds 0) := by
  apply squeeze_zero' (g := fun n : ℕ => ((Nat.log 2 (3 * n) + 1 : ℕ) : ℝ) / n)
  · filter_upwards with n
    unfold GenLimit.KleinbergWei.OrderedLanguage.prefixRatio
    positivity
  · filter_upwards [eventually_gt_atTop 0] with n hn
    rw [GenLimit.KleinbergWei.OrderedLanguage.prefixRatio, if_neg (Nat.ne_of_gt hn)]
    have hc := core_prefixCount_le_log gen n
    exact div_le_div_of_nonneg_right (by exact_mod_cast hc) (by positivity)
  · exact log_ratio_tendsto_zero

 theorem core_upperDensity_zero (gen : FeedbackGenerator) :
    (orderedK gen).upperDensity core = 0 := by
  exact (core_prefixRatio_tendsto_zero gen).limsup_eq

def code (n : ℕ) := 2 ^ (n + 1) + 1

theorem code_injective : Function.Injective code := by
  intro m n h
  have hp : 2 ^ (m + 1) = 2 ^ (n + 1) := by
    simpa [code] using Nat.add_right_cancel h
  have := Nat.pow_right_injective (by omega : 1 < 2) hp
  omega

theorem code_not_core (n : ℕ) : code n ∉ core := by
  rintro ⟨k, hk⟩
  change 2 ^ k = 2 ^ (n + 1) + 1 at hk
  have hlo : 2 ^ (n + 1) < 2 ^ k := by omega
  have hp : 2 ≤ 2 ^ (n + 1) := by
    exact Nat.one_lt_pow (by omega) (by omega)
  have hhi : 2 ^ k < 2 ^ (n + 2) := by
    rw [hk, show n + 2 = (n + 1) + 1 by omega, pow_succ]
    omega
  have hklo : n + 1 < k := (Nat.pow_lt_pow_iff_right (by omega)).mp hlo
  have hkhi : k < n + 2 := (Nat.pow_lt_pow_iff_right (by omega)).mp hhi
  omega

theorem uncountable_targetClass : ¬ targetClass.Countable := by
  intro hcount
  have hnonempty : targetClass.Nonempty := by
    refine ⟨core, ∅, ?_, ?_⟩
    · exact Set.empty_subset _
    · simp
  rcases hcount.exists_eq_range hnonempty with ⟨f, hf⟩
  let A : Language := code '' {n | code n ∉ f n}
  let L : Language := core ∪ A
  have hL : L ∈ targetClass := by
    refine ⟨A, ?_, rfl⟩
    rintro z ⟨n, hn, rfl⟩
    exact code_not_core n
  rw [hf] at hL
  rcases hL with ⟨m, hm⟩
  have hdiag : code m ∈ L ↔ code m ∉ f m := by
    simp only [L, A, Set.mem_union, Set.mem_image, Set.mem_setOf_eq]
    constructor
    · rintro (hc | ⟨n, hn, heq⟩)
      · exact False.elim (code_not_core m hc)
      · have : n = m := code_injective heq
        simpa [this] using hn
    · intro hn
      exact Or.inr ⟨m, hn, rfl⟩
  have hmem : code m ∈ f m ↔ code m ∈ L := by
    constructor <;> intro h <;> simpa only [hm] using h
  have : code m ∈ f m ↔ code m ∉ f m := hmem.trans hdiag
  tauto

theorem prefixCount_mono {K : OrderedLanguage} {A B : Language}
    (hAB : A ⊆ B) (n : ℕ) : K.prefixCount A n ≤ K.prefixCount B n := by
  classical
  unfold GenLimit.KleinbergWei.OrderedLanguage.prefixCount
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢
  exact ⟨hi.1, hAB hi.2⟩

theorem prefixRatio_mono {K : OrderedLanguage} {A B : Language}
    (hAB : A ⊆ B) (n : ℕ) : K.prefixRatio A n ≤ K.prefixRatio B n := by
  rw [GenLimit.KleinbergWei.OrderedLanguage.prefixRatio,
    GenLimit.KleinbergWei.OrderedLanguage.prefixRatio]
  split
  · simp
  · exact div_le_div_of_nonneg_right (by exact_mod_cast prefixCount_mono hAB n) (by positivity)

theorem scored_prefixRatio_tendsto_zero (gen : FeedbackGenerator) :
    Tendsto ((orderedK gen).prefixRatio (scored (K gen) (x gen) (y gen)))
      atTop (nhds 0) := by
  apply squeeze_zero' (g := (orderedK gen).prefixRatio core)
  · filter_upwards with n
    unfold GenLimit.KleinbergWei.OrderedLanguage.prefixRatio
    positivity
  · filter_upwards with n
    exact prefixRatio_mono (scored_subset_core gen) n
  · exact core_prefixRatio_tendsto_zero gen

theorem scored_upperDensity_zero (gen : FeedbackGenerator) :
    (orderedK gen).upperDensity (scored (K gen) (x gen) (y gen)) = 0 := by
  exact (scored_prefixRatio_tendsto_zero gen).limsup_eq

theorem negative : NegativeClaim := by
  intro gen _
  refine ⟨K gen, K_targetClass gen, presenter gen, tr gen, orderedK gen, ?_⟩
  exact ⟨rfl, orderedK_inherits gen, presented gen, follows gen,
    clean_x gen, x_injective gen, complete_x gen, scored_upperDensity_zero gen⟩


theorem positive : UniformlyGeneratableWithoutSamples := by
  refine ⟨fun t => 2 ^ t, ?_, 0, ?_⟩
  · exact Nat.pow_right_injective (by omega)
  · intro K hK t _
    rcases hK with ⟨A, hA, rfl⟩
    exact Or.inl ⟨t, rfl⟩

end Stage3Proof

theorem stage3_result : Stage3S2B.MainClaim := by
  exact ⟨Stage3Proof.uncountable_targetClass, Stage3Proof.positive, Stage3Proof.negative⟩
