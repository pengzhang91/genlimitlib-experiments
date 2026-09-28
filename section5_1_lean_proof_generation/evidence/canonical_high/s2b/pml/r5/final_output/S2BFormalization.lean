import Stage3Model
import GenLimit.Paper10_UnionClosednessOfLanguageGeneration.Cardinality
import GenLimit.Paper39_DenseGeneration.Abstract.Density

open Set Filter
open scoped Topology

namespace Stage3Proof

open Stage3S2B

noncomputable section

open Classical

def fresh (s : Finset ℕ) : ℕ :=
  Nat.find (Set.infinite_univ.exists_notMem_finset s)

theorem fresh_not_mem (s : Finset ℕ) : fresh s ∉ s := by
  exact (Nat.find_spec (Set.infinite_univ.exists_notMem_finset s)).2

theorem lt_fresh_mem (s : Finset ℕ) {n : ℕ} (hn : n < fresh s) : n ∈ s := by
  by_contra h
  exact Nat.find_min (Set.infinite_univ.exists_notMem_finset s) hn ⟨Set.mem_univ n, h⟩

theorem fresh_le_card (s : Finset ℕ) : fresh s ≤ s.card := by
  by_contra h
  have hsub : Finset.range (fresh s) ⊆ s := by
    intro n hn
    exact lt_fresh_mem s (Finset.mem_range.mp hn)
  have hc := Finset.card_le_card hsub
  simp only [Finset.card_range] at hc
  omega

structure Hist (t : ℕ) where
  presentation : Fin t → ℕ
  query : Fin t → Option ℕ
  answer : Fin t → Option Bool
  output : Fin t → ℕ
  blocked : Finset ℕ

def Hist.empty : Hist 0 where
  presentation := Fin.elim0
  query := Fin.elim0
  answer := Fin.elim0
  output := Fin.elim0
  blocked := ∅

def roundPresentation {t : ℕ} (h : Hist t) : ℕ := fresh h.blocked

def extendedPresentation {t : ℕ} (h : Hist t) : Fin (t + 1) → ℕ :=
  Fin.lastCases (roundPresentation h) h.presentation

def roundQuery (gen : FeedbackGenerator) {t : ℕ} (h : Hist t) : Option ℕ :=
  gen.query t (extendedPresentation h) h.answer

def roundAnswer (gen : FeedbackGenerator) {t : ℕ} (h : Hist t) : Option Bool :=
  (roundQuery gen h).map fun z =>
    decide (z ∈ core ∨ ∃ i, extendedPresentation h i = z)

def extendedAnswer (gen : FeedbackGenerator) {t : ℕ} (h : Hist t) :
    Fin (t + 1) → Option Bool :=
  Fin.lastCases (roundAnswer gen h) h.answer

def roundOutput (gen : FeedbackGenerator) {t : ℕ} (h : Hist t) : ℕ :=
  gen.output t (extendedPresentation h) (extendedAnswer gen h)

def queryBlocked (gen : FeedbackGenerator) {t : ℕ} (h : Hist t) : Finset ℕ :=
  match roundQuery gen h, roundAnswer gen h with
  | some z, some false => insert z (insert (roundPresentation h) h.blocked)
  | _, _ => insert (roundPresentation h) h.blocked

def nextBlocked (gen : FeedbackGenerator) {t : ℕ} (h : Hist t) : Finset ℕ :=
  if roundOutput gen h ∈ ordinary then
    insert (roundOutput gen h) (queryBlocked gen h)
  else queryBlocked gen h

def Hist.next (gen : FeedbackGenerator) {t : ℕ} (h : Hist t) : Hist (t + 1) where
  presentation := extendedPresentation h
  query := Fin.lastCases (roundQuery gen h) h.query
  answer := extendedAnswer gen h
  output := Fin.lastCases (roundOutput gen h) h.output
  blocked := nextBlocked gen h

def history (gen : FeedbackGenerator) : (t : ℕ) → Hist t
  | 0 => Hist.empty
  | t + 1 => (history gen t).next gen

def presentation (gen : FeedbackGenerator) (t : ℕ) : ℕ :=
  roundPresentation (history gen t)

def query (gen : FeedbackGenerator) (t : ℕ) : Option ℕ :=
  roundQuery gen (history gen t)

def answer (gen : FeedbackGenerator) (t : ℕ) : Option Bool :=
  roundAnswer gen (history gen t)

def output (gen : FeedbackGenerator) (t : ℕ) : ℕ :=
  roundOutput gen (history gen t)

def transcript (gen : FeedbackGenerator) : Transcript where
  presentation := presentation gen
  query := query gen
  answer := answer gen
  output := output gen

def target (gen : FeedbackGenerator) : Language := Set.range (presentation gen)

def presenter (gen : FeedbackGenerator) : CausalPresenter where
  next t _ _ _ _ := presentation gen t

@[simp] theorem history_succ (gen : FeedbackGenerator) (t : ℕ) :
    history gen (t + 1) = (history gen t).next gen := rfl

@[simp] theorem history_presentation (gen : FeedbackGenerator) (t : ℕ)
    (i : Fin t) : (history gen t).presentation i = presentation gen i := by
  induction t with
  | zero => exact Fin.elim0 i
  | succ t ih =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [history, Hist.next, extendedPresentation, presentation]
      · simpa [history, Hist.next, extendedPresentation] using ih j

@[simp] theorem history_query (gen : FeedbackGenerator) (t : ℕ)
    (i : Fin t) : (history gen t).query i = query gen i := by
  induction t with
  | zero => exact Fin.elim0 i
  | succ t ih =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [history, Hist.next, query]
      · simpa [history, Hist.next] using ih j

@[simp] theorem history_answer (gen : FeedbackGenerator) (t : ℕ)
    (i : Fin t) : (history gen t).answer i = answer gen i := by
  induction t with
  | zero => exact Fin.elim0 i
  | succ t ih =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [history, Hist.next, extendedAnswer, answer]
      · simpa [history, Hist.next, extendedAnswer] using ih j

@[simp] theorem history_output (gen : FeedbackGenerator) (t : ℕ)
    (i : Fin t) : (history gen t).output i = output gen i := by
  induction t with
  | zero => exact Fin.elim0 i
  | succ t ih =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [history, Hist.next, output]
      · simpa [history, Hist.next] using ih j

@[simp] theorem extendedPresentation_eq (gen : FeedbackGenerator) (t : ℕ) :
    extendedPresentation (history gen t) = fun i : Fin (t + 1) => presentation gen i := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [extendedPresentation, presentation]
  · simp [extendedPresentation, history_presentation]

@[simp] theorem extendedAnswer_eq (gen : FeedbackGenerator) (t : ℕ) :
    extendedAnswer gen (history gen t) = fun i : Fin (t + 1) => answer gen i := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [extendedAnswer, answer]
  · simp [extendedAnswer, history_answer]

 theorem presentedBy (gen : FeedbackGenerator) :
    PresentedBy (presenter gen) (transcript gen) := by
  intro t
  rfl

theorem query_protocol (gen : FeedbackGenerator) (t : ℕ) :
    query gen t = gen.query t (fun i => presentation gen i) (fun i => answer gen i) := by
  unfold query roundQuery
  rw [extendedPresentation_eq]
  congr 1
  funext i
  exact history_answer gen t i

theorem output_protocol (gen : FeedbackGenerator) (t : ℕ) :
    output gen t = gen.output t (fun i => presentation gen i) (fun i => answer gen i) := by
  simp [output, roundOutput]

theorem queryBlocked_card (gen : FeedbackGenerator) {t : ℕ} (h : Hist t) :
    (queryBlocked gen h).card ≤ h.blocked.card + 2 := by
  rcases hq : roundQuery gen h with _ | z
  · simp only [queryBlocked, hq]
    have := Finset.card_insert_le (roundPresentation h) h.blocked
    omega
  · rcases ha : roundAnswer gen h with _ | a
    · simp only [queryBlocked, hq, ha]
      have := Finset.card_insert_le (roundPresentation h) h.blocked
      omega
    · cases a <;> simp only [queryBlocked, hq, ha]
      · exact (Finset.card_insert_le _ _).trans (by
          have := Finset.card_insert_le (roundPresentation h) h.blocked
          omega)
      · have := Finset.card_insert_le (roundPresentation h) h.blocked
        omega

theorem nextBlocked_card (gen : FeedbackGenerator) {t : ℕ} (h : Hist t) :
    (nextBlocked gen h).card ≤ h.blocked.card + 3 := by
  unfold nextBlocked
  split
  · exact (Finset.card_insert_le _ _).trans (by
      have := queryBlocked_card gen h
      omega)
  · have := queryBlocked_card gen h
    omega

theorem blocked_card (gen : FeedbackGenerator) (t : ℕ) :
    (history gen t).blocked.card ≤ 3 * t := by
  induction t with
  | zero => simp [history, Hist.empty]
  | succ t ih =>
      rw [history_succ]
      simp only [Hist.next]
      have hstep := nextBlocked_card gen (history gen t)
      omega

theorem presentation_le (gen : FeedbackGenerator) (t : ℕ) :
    presentation gen t ≤ 3 * t := by
  exact (fresh_le_card _).trans (blocked_card gen t)

theorem blocked_subset_queryBlocked (gen : FeedbackGenerator) {t : ℕ} (h : Hist t) :
    h.blocked ⊆ queryBlocked gen h := by
  rcases hq : roundQuery gen h with _ | z
  · simp [queryBlocked, hq]
  · rcases ha : roundAnswer gen h with _ | a
    · simp [queryBlocked, hq, ha]
    · cases a
      · intro x hx
        simp [queryBlocked, hq, ha, hx]
      · intro x hx
        simp [queryBlocked, hq, ha, hx]

theorem presentation_mem_queryBlocked (gen : FeedbackGenerator) {t : ℕ} (h : Hist t) :
    roundPresentation h ∈ queryBlocked gen h := by
  rcases hq : roundQuery gen h with _ | z
  · simp [queryBlocked, hq]
  · rcases ha : roundAnswer gen h with _ | a
    · simp [queryBlocked, hq, ha]
    · cases a <;> simp [queryBlocked, hq, ha]

theorem queryBlocked_subset_nextBlocked (gen : FeedbackGenerator) {t : ℕ} (h : Hist t) :
    queryBlocked gen h ⊆ nextBlocked gen h := by
  unfold nextBlocked
  split <;> simp

theorem blocked_mono (gen : FeedbackGenerator) (t : ℕ) :
    (history gen t).blocked ⊆ (history gen (t + 1)).blocked := by
  rw [history_succ]
  exact (blocked_subset_queryBlocked gen _).trans (queryBlocked_subset_nextBlocked gen _)

theorem presentation_mem_next_blocked (gen : FeedbackGenerator) (t : ℕ) :
    presentation gen t ∈ (history gen (t + 1)).blocked := by
  rw [history_succ]
  exact queryBlocked_subset_nextBlocked gen _ (presentation_mem_queryBlocked gen _)

theorem blocked_persists (gen : FeedbackGenerator) {s t : ℕ} (hst : s ≤ t) :
    (history gen s).blocked ⊆ (history gen t).blocked := by
  induction t, hst using Nat.le_induction with
  | base => exact fun _ h => h
  | succ t hst ih => exact fun z hz => blocked_mono gen t (ih hz)

theorem presentation_ne_of_lt (gen : FeedbackGenerator) {s t : ℕ} (hst : s < t) :
    presentation gen s ≠ presentation gen t := by
  intro h
  have hm : presentation gen s ∈ (history gen t).blocked :=
    blocked_persists gen (Nat.succ_le_iff.mp hst) (presentation_mem_next_blocked gen s)
  have hn := fresh_not_mem (history gen t).blocked
  apply hn
  have hx : presentation gen t ∈ (history gen t).blocked := h ▸ hm
  simpa [presentation, roundPresentation] using hx

theorem presentation_injective (gen : FeedbackGenerator) :
    Function.Injective (presentation gen) := by
  intro s t h
  rcases lt_trichotomy s t with hst | hst | hst
  · exact False.elim (presentation_ne_of_lt gen hst h)
  · exact hst
  · exact False.elim (presentation_ne_of_lt gen hst h.symm)


theorem presentation_strictMono (gen : FeedbackGenerator) :
    StrictMono (presentation gen) := by
  intro s t hst
  have hne := presentation_ne_of_lt gen hst
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact hlt
  · have hm : presentation gen t ∈ (history gen s).blocked := by
      exact lt_fresh_mem _ (by simpa [presentation, roundPresentation] using hgt)
    have hmt : presentation gen t ∈ (history gen t).blocked :=
      blocked_persists gen (Nat.le_of_lt hst) hm
    exact False.elim (fresh_not_mem (history gen t).blocked
      (by simpa [presentation, roundPresentation] using hmt))

theorem false_query_not_core (gen : FeedbackGenerator) {t : ℕ} (h : Hist t) {z : ℕ}
    (hq : roundQuery gen h = some z) (ha : roundAnswer gen h = some false) :
    z ∉ core := by
  simp [roundAnswer, hq] at ha
  exact ha.1

theorem core_mem_queryBlocked (gen : FeedbackGenerator) {t : ℕ} (h : Hist t) {z : ℕ}
    (hzcore : z ∈ core) (hz : z ∈ queryBlocked gen h) :
    z ∈ h.blocked ∨ z = roundPresentation h := by
  rcases hq : roundQuery gen h with _ | q
  · simp only [queryBlocked, hq, Finset.mem_insert] at hz
    exact hz.symm
  · rcases ha : roundAnswer gen h with _ | a
    · simp only [queryBlocked, hq, ha, Finset.mem_insert] at hz
      exact hz.symm
    · cases a
      · simp only [queryBlocked, hq, ha, Finset.mem_insert] at hz
        rcases hz with rfl | hz
        · exact False.elim (false_query_not_core gen h hq ha hzcore)
        · exact hz.symm
      · simp only [queryBlocked, hq, ha, Finset.mem_insert] at hz
        exact hz.symm

theorem core_mem_blocked_presented (gen : FeedbackGenerator) (t : ℕ) {z : ℕ}
    (hzcore : z ∈ core) (hz : z ∈ (history gen t).blocked) :
    ∃ i : Fin t, presentation gen i = z := by
  induction t with
  | zero => simp [history, Hist.empty] at hz
  | succ t ih =>
      rw [history_succ] at hz
      simp only [Hist.next] at hz
      have hzq : z ∈ queryBlocked gen (history gen t) := by
        unfold nextBlocked at hz
        split at hz
        · simp only [Finset.mem_insert] at hz
          rcases hz with hy | hz
          · subst z
            rename_i hout
            have hord : output gen t ∈ ordinary := by simpa [output] using hout
            exact False.elim (hord hzcore)
          · exact hz
        · exact hz
      rcases core_mem_queryBlocked gen (history gen t) hzcore hzq with hold | hcurrent
      · obtain ⟨i, hi⟩ := ih hold
        exact ⟨i.castSucc, by simpa using hi⟩
      · exact ⟨Fin.last t, by simpa [presentation, roundPresentation] using hcurrent.symm⟩

theorem core_subset_target (gen : FeedbackGenerator) : core ⊆ target gen := by
  intro z hzcore
  have hzt : z < presentation gen (z + 1) := by
    have hid : z + 1 ≤ presentation gen (z + 1) :=
      (presentation_strictMono gen).id_le (z + 1)
    omega
  have hzblocked : z ∈ (history gen (z + 1)).blocked :=
    lt_fresh_mem _ (by simpa [presentation, roundPresentation] using hzt)
  obtain ⟨i, hi⟩ := core_mem_blocked_presented gen (z + 1) hzcore hzblocked
  exact ⟨i, hi⟩

theorem target_mem_class (gen : FeedbackGenerator) : target gen ∈ targetClass := by
  refine ⟨target gen \ core, ?_, ?_⟩
  · exact Set.diff_subset_compl (target gen) core
  · ext z
    constructor
    · intro hz
      by_cases hzcore : z ∈ core
      · exact Or.inl hzcore
      · exact Or.inr ⟨hz, hzcore⟩
    · intro hz
      rcases hz with hz | hz
      · exact core_subset_target gen hz
      · exact hz.1


theorem false_query_mem_next_blocked (gen : FeedbackGenerator) (t z : ℕ)
    (hq : query gen t = some z) (ha : answer gen t = some false) :
    z ∈ (history gen (t + 1)).blocked := by
  rw [history_succ]
  apply queryBlocked_subset_nextBlocked gen
  have hq' : roundQuery gen (history gen t) = some z := hq
  have ha' : roundAnswer gen (history gen t) = some false := ha
  simp [queryBlocked, hq', ha']

theorem queried_target_iff (gen : FeedbackGenerator) (t z : ℕ)
    (hq : query gen t = some z) :
    z ∈ target gen ↔ z ∈ core ∨ ∃ i : Fin (t + 1), presentation gen i = z := by
  constructor
  · rintro ⟨s, hs⟩
    by_cases hzcore : z ∈ core
    · exact Or.inl hzcore
    by_cases hst : s ≤ t
    · exact Or.inr ⟨⟨s, Nat.lt_succ_iff.mpr hst⟩, hs⟩
    · have hprefix : ¬ ∃ i : Fin (t + 1), presentation gen i = z := by
        rintro ⟨i, hi⟩
        have heq : (i : ℕ) = s := presentation_injective gen (hi.trans hs.symm)
        exact hst (by omega)
      have ha : answer gen t = some false := by
        have hq' : roundQuery gen (history gen t) = some z := hq
        unfold answer roundAnswer
        rw [hq']
        simp only [Option.map_some, Option.some.injEq]
        apply decide_eq_false
        rintro (hc | ⟨i, hi⟩)
        · exact hzcore hc
        · exact hprefix ⟨i, by simpa using hi⟩
      have hzblocked := false_query_mem_next_blocked gen t z hq ha
      have hzblocked' : z ∈ (history gen s).blocked :=
        blocked_persists gen (Nat.succ_le_iff.mpr (Nat.lt_of_not_ge hst)) hzblocked
      have hnot := fresh_not_mem (history gen s).blocked
      rw [← hs] at hzblocked'
      exact False.elim (hnot (by simpa [presentation, roundPresentation] using hzblocked'))
  · rintro (hz | ⟨i, hi⟩)
    · exact core_subset_target gen hz
    · exact ⟨i, hi⟩

theorem answer_protocol (gen : FeedbackGenerator) (t : ℕ) :
    answer gen t = match query gen t with
      | none => none
      | some z => some (membershipAnswer (target gen) z) := by
  rcases hq : query gen t with _ | z
  · have hq' : roundQuery gen (history gen t) = none := hq
    simp [answer, roundAnswer, hq']
  · have hq' : roundQuery gen (history gen t) = some z := hq
    unfold answer roundAnswer
    rw [hq']
    simp only [Option.map_some, membershipAnswer]
    congr 2
    apply propext
    simpa [extendedPresentation_eq] using
      (queried_target_iff gen t z hq).symm

theorem followsProtocol (gen : FeedbackGenerator) :
    FollowsProtocol gen (target gen) (transcript gen) := by
  intro t
  exact ⟨query_protocol gen t, answer_protocol gen t, output_protocol gen t⟩

theorem clean (gen : FeedbackGenerator) :
    Clean (presentation gen) (target gen) := by
  intro t
  exact ⟨t, rfl⟩

theorem complete (gen : FeedbackGenerator) :
    Complete (presentation gen) (target gen) := by
  intro z hz
  exact hz

theorem output_ordinary_mem_next_blocked (gen : FeedbackGenerator) (t : ℕ)
    (hord : output gen t ∈ ordinary) :
    output gen t ∈ (history gen (t + 1)).blocked := by
  rw [history_succ]
  simp only [Hist.next]
  unfold nextBlocked
  rw [if_pos (by simpa [output] using hord)]
  exact Finset.mem_insert_self _ _

theorem scored_subset_core (gen : FeedbackGenerator) :
    scored (target gen) (presentation gen) (output gen) ⊆ core := by
  intro z hz
  rcases hz with ⟨⟨s, hs⟩, t, ht, hnot⟩
  by_contra hzcore
  have hord : z ∈ ordinary := hzcore
  have hts : t < s := by
    by_contra h
    have hst : s ≤ t := Nat.le_of_not_gt h
    apply hnot
    exact ⟨s, hst, hs⟩
  have hzblocked : z ∈ (history gen (t + 1)).blocked := by
    simpa [ht] using output_ordinary_mem_next_blocked gen t (by simpa [ht] using hord)
  have hzblocked' : z ∈ (history gen s).blocked :=
    blocked_persists gen (Nat.succ_le_iff.mpr hts) hzblocked
  rw [← hs] at hzblocked'
  exact fresh_not_mem (history gen s).blocked
    (by simpa [presentation, roundPresentation] using hzblocked')


def coreExponent (z : ℕ) : ℕ :=
  if h : z ∈ core then Nat.find h else 0

theorem pow_coreExponent {z : ℕ} (hz : z ∈ core) :
    2 ^ coreExponent z = z := by
  rw [coreExponent, dif_pos hz]
  exact Nat.find_spec hz

theorem log2_four_mul (n : ℕ) (hn : n ≠ 0) :
    Nat.log2 (4 * n) = Nat.log2 n + 2 := by
  rw [Nat.log2_eq_log_two, show 4 * n = (n * 2) * 2 by omega]
  rw [Nat.log_mul_base Nat.one_lt_two (mul_ne_zero hn (by norm_num))]
  rw [Nat.log_mul_base Nat.one_lt_two hn, Nat.log2_eq_log_two]

theorem prefixCount_core_le (gen : FeedbackGenerator) (n : ℕ) :
    let orderedK : OrderedLanguage := {
      carrier := target gen
      enumeration := presentation gen
      enumeration_injective := presentation_injective gen
      range_enumeration := rfl }
    orderedK.prefixCount core n ≤ 3 + Nat.log2 n := by
  let S := (Finset.range n).filter fun i => presentation gen i ∈ core
  let e : ℕ → ℕ := fun i => coreExponent (presentation gen i)
  have hinj : Set.InjOn e (S : Set ℕ) := by
    intro i hi j hj hij
    apply presentation_injective gen
    have hiCore : presentation gen i ∈ core := (Finset.mem_filter.mp hi).2
    have hjCore : presentation gen j ∈ core := (Finset.mem_filter.mp hj).2
    calc
      presentation gen i = 2 ^ e i := (pow_coreExponent hiCore).symm
      _ = 2 ^ e j := by rw [hij]
      _ = presentation gen j := pow_coreExponent hjCore
  by_cases hn : n = 0
  · simp [GenLimit.KleinbergWei.OrderedLanguage.prefixCount, hn]
  have himage : Finset.image e S ⊆ Finset.range (Nat.log2 (4 * n) + 1) := by
    intro k hk
    simp only [Finset.mem_image] at hk
    obtain ⟨i, hiS, rfl⟩ := hk
    have hi : i < n := Finset.mem_range.mp (Finset.mem_filter.mp hiS).1
    have hiCore : presentation gen i ∈ core := (Finset.mem_filter.mp hiS).2
    have hpow : 2 ^ e i ≤ 4 * n := by
      rw [show 2 ^ e i = presentation gen i by exact pow_coreExponent hiCore]
      calc
        presentation gen i ≤ 3 * i := presentation_le gen i
        _ ≤ 4 * n := by omega
    have hlog : e i ≤ Nat.log2 (4 * n) :=
      (Nat.le_log2 (by positivity)).2 hpow
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le hlog)
  have hcardImage : (Finset.image e S).card = S.card :=
    Finset.card_image_iff.mpr hinj
  have hcard : S.card ≤ Nat.log2 (4 * n) + 1 := by
    rw [← hcardImage]
    exact (Finset.card_le_card himage).trans (by simp)
  have hlog := log2_four_mul n hn
  change S.card ≤ 3 + Nat.log2 n
  omega

def orderedTarget (gen : FeedbackGenerator) : OrderedLanguage where
  carrier := target gen
  enumeration := presentation gen
  enumeration_injective := presentation_injective gen
  range_enumeration := rfl

theorem core_upperDensity_zero (gen : FeedbackGenerator) :
    (orderedTarget gen).upperDensity core = 0 := by
  have hbound : ∀ n,
      (orderedTarget gen).prefixRatio core n ≤
        ((3 + Nat.log2 n : ℕ) : ℝ) / (n : ℝ) := by
    intro n
    by_cases hn : n = 0
    · simp [hn]
    · simp only [GenLimit.KleinbergWei.OrderedLanguage.prefixRatio, hn, if_false]
      apply div_le_div_of_nonneg_right
      · exact_mod_cast prefixCount_core_le gen n
      · positivity
  have htendsto : Tendsto ((orderedTarget gen).prefixRatio core) atTop (nhds 0) := by
    apply squeeze_zero
      (fun n => (orderedTarget gen).prefixRatio_nonneg core n) hbound
    exact GenLimit.tendsto_countingError_div 3
  exact htendsto.limsup_eq

theorem scored_upperDensity_zero (gen : FeedbackGenerator) :
    (orderedTarget gen).upperDensity
      (scored (target gen) (presentation gen) (output gen)) = 0 := by
  apply le_antisymm
  · calc
      (orderedTarget gen).upperDensity
          (scored (target gen) (presentation gen) (output gen))
          ≤ (orderedTarget gen).upperDensity core :=
            (orderedTarget gen).upperDensity_mono (scored_subset_core gen)
      _ = 0 := core_upperDensity_zero gen
  · exact (orderedTarget gen).upperDensity_nonneg _

def oddCode (n : ℕ) : ℕ := 2 * n + 3

theorem oddCode_injective : Function.Injective oddCode := by
  intro m n h
  simp only [oddCode] at h
  omega

theorem oddCode_mem_ordinary (n : ℕ) : oddCode n ∈ ordinary := by
  intro hcore
  rcases hcore with ⟨k, hk⟩
  cases k with
  | zero => simp [oddCode] at hk
  | succ k =>
      simp only [pow_succ] at hk
      simp only [oddCode] at hk
      omega

def encodedLanguage (A : Set ℕ) : Language := core ∪ oddCode '' A

theorem encodedLanguage_mem_class (A : Set ℕ) : encodedLanguage A ∈ targetClass := by
  refine ⟨oddCode '' A, ?_, rfl⟩
  rintro z ⟨n, hn, rfl⟩
  exact oddCode_mem_ordinary n

theorem oddCode_mem_encodedLanguage_iff (A : Set ℕ) (n : ℕ) :
    oddCode n ∈ encodedLanguage A ↔ n ∈ A := by
  constructor
  · rintro (hcore | ⟨m, hm, hmn⟩)
    · exact False.elim ((oddCode_mem_ordinary n) hcore)
    · exact oddCode_injective hmn ▸ hm
  · intro hn
    exact Or.inr ⟨n, hn, rfl⟩

def encodedTarget (A : Set ℕ) : {K : Language // K ∈ targetClass} :=
  ⟨encodedLanguage A, encodedLanguage_mem_class A⟩

theorem encodedTarget_injective : Function.Injective encodedTarget := by
  intro A B h
  have hsets : encodedLanguage A = encodedLanguage B := congrArg Subtype.val h
  ext n
  have hmem := Set.ext_iff.mp hsets (oddCode n)
  simpa only [oddCode_mem_encodedLanguage_iff] using hmem

theorem targetClass_not_countable : ¬ targetClass.Countable := by
  intro hcountable
  letI : Countable {K : Language // K ∈ targetClass} := hcountable.to_subtype
  have hpower : Countable (Set ℕ) := encodedTarget_injective.countable
  exact GenLimit.UnionClosedness.powerSet_not_countable ℕ hpower

theorem uniformlyGeneratableWithoutSamples : UniformlyGeneratableWithoutSamples := by
  refine ⟨fun t => 2 ^ t, Nat.pow_right_injective (by norm_num), 0, ?_⟩
  intro K hK t ht
  rcases hK with ⟨A, hA, rfl⟩
  exact Or.inl ⟨t, rfl⟩

theorem negativeClaim : NegativeClaim := by
  intro gen hgen
  refine ⟨target gen, target_mem_class gen, presenter gen, transcript gen,
    orderedTarget gen, ?_⟩
  exact ⟨rfl, presentation_strictMono gen, presentedBy gen,
    followsProtocol gen, clean gen, presentation_injective gen,
    complete gen, scored_upperDensity_zero gen⟩

end

end Stage3Proof

theorem stage3_result : Stage3S2B.MainClaim := by
  exact ⟨Stage3Proof.targetClass_not_countable,
    Stage3Proof.uniformlyGeneratableWithoutSamples,
    Stage3Proof.negativeClaim⟩
