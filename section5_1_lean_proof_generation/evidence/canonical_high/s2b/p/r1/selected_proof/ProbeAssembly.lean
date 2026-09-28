import Stage3Model
import Mathlib.Data.Nat.Nth
import Mathlib.Algebra.Ring.Parity
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Data.Real.Sqrt

open Set Filter
open scoped Topology

namespace Stage3Proof

open Stage3S2B

structure SimState (t : ℕ) where
  presentation : Fin t → ℕ
  query : Fin t → Option ℕ
  answer : Fin t → Option Bool
  output : Fin t → ℕ

private def emptyState : SimState 0 :=
  ⟨Fin.elim0, Fin.elim0, Fin.elim0, Fin.elim0⟩

private def forbidden {t : ℕ} (s : SimState t) : Finset ℕ := by
  classical
  exact (Finset.univ.image s.presentation ∪ Finset.univ.image (fun i => (s.query i).getD 0)) ∪
    Finset.univ.image s.output

private def candidates (t : ℕ) : Finset ℕ :=
  (Finset.range (3 * t + 1)).image (fun i => 2 * i + 3)

private lemma candidate_map_injective : Function.Injective (fun i : ℕ => 2 * i + 3) := by
  intro m n h
  have h' : 2 * m = 2 * n := Nat.add_right_cancel h
  exact Nat.mul_left_cancel (by omega) h'

private lemma card_candidates (t : ℕ) : (candidates t).card = 3 * t + 1 := by
  classical
  rw [candidates, Finset.card_image_of_injective _ candidate_map_injective, Finset.card_range]

private lemma card_forbidden_le {t : ℕ} (s : SimState t) : (forbidden s).card ≤ 3 * t := by
  classical
  unfold forbidden
  calc
    ((Finset.univ.image s.presentation ∪ Finset.univ.image fun i => (s.query i).getD 0) ∪
        Finset.univ.image s.output).card
        ≤ (Finset.univ.image s.presentation ∪ Finset.univ.image fun i => (s.query i).getD 0).card +
          (Finset.univ.image s.output).card := Finset.card_union_le _ _
    _ ≤ ((Finset.univ.image s.presentation).card +
          (Finset.univ.image fun i => (s.query i).getD 0).card) +
          (Finset.univ.image s.output).card := Nat.add_le_add_right (Finset.card_union_le _ _) _
    _ ≤ ((Finset.univ : Finset (Fin t)).card + (Finset.univ : Finset (Fin t)).card) +
          (Finset.univ : Finset (Fin t)).card := by
      exact Nat.add_le_add (Nat.add_le_add Finset.card_image_le Finset.card_image_le)
        Finset.card_image_le
    _ = 3 * t := by simp; omega

private lemma exists_fresh_candidate {t : ℕ} (s : SimState t) :
    ∃ z, z ∈ candidates t ∧ z ∉ forbidden s := by
  have hcard : (forbidden s).card < (candidates t).card := by
    rw [card_candidates]
    exact lt_of_le_of_lt (card_forbidden_le s) (by omega)
  exact Finset.exists_mem_not_mem_of_card_lt_card hcard

private noncomputable def freshCandidate {t : ℕ} (s : SimState t) : ℕ :=
  Classical.choose (exists_fresh_candidate s)

private lemma freshCandidate_mem {t : ℕ} (s : SimState t) : freshCandidate s ∈ candidates t :=
  (Classical.choose_spec (exists_fresh_candidate s)).1

private lemma freshCandidate_not_forbidden {t : ℕ} (s : SimState t) :
    freshCandidate s ∉ forbidden s :=
  (Classical.choose_spec (exists_fresh_candidate s)).2

private noncomputable def choosePresentation {t : ℕ} (s : SimState t) : ℕ :=
  if Even t then 2 ^ (t / 2) else freshCandidate s

private noncomputable def extendPresentation {t : ℕ} (s : SimState t) : Fin (t + 1) → ℕ :=
  Fin.snoc s.presentation (choosePresentation s)

private noncomputable def makeRound (gen : FeedbackGenerator) {t : ℕ} (s : SimState t) :
    Option ℕ × Option Bool × ℕ := by
  let xp := extendPresentation s
  let q := gen.query t xp s.answer
  let a := match q with
    | none => none
    | some z => some (membershipAnswer (core ∪ Set.range xp) z)
  let ap := Fin.snoc (α := fun _ => Option Bool) s.answer a
  exact (q, a, gen.output t xp ap)

private noncomputable def step (gen : FeedbackGenerator) {t : ℕ} (s : SimState t) :
    SimState (t + 1) := by
  let r := makeRound gen s
  exact {
    presentation := extendPresentation s
    query := Fin.snoc s.query r.1
    answer := Fin.snoc s.answer r.2.1
    output := Fin.snoc s.output r.2.2
  }

private noncomputable def run (gen : FeedbackGenerator) : (t : ℕ) → SimState t
  | 0 => emptyState
  | t + 1 => step gen (run gen t)

private noncomputable def x (gen : FeedbackGenerator) (t : ℕ) : ℕ :=
  choosePresentation (run gen t)

private noncomputable def q (gen : FeedbackGenerator) (t : ℕ) : Option ℕ :=
  (makeRound gen (run gen t)).1

private noncomputable def a (gen : FeedbackGenerator) (t : ℕ) : Option Bool :=
  (makeRound gen (run gen t)).2.1

private noncomputable def y (gen : FeedbackGenerator) (t : ℕ) : ℕ :=
  (makeRound gen (run gen t)).2.2

private lemma run_history (gen : FeedbackGenerator) (t : ℕ) :
    (∀ i : Fin t, (run gen t).presentation i = x gen i) ∧
    (∀ i : Fin t, (run gen t).query i = q gen i) ∧
    (∀ i : Fin t, (run gen t).answer i = a gen i) ∧
    (∀ i : Fin t, (run gen t).output i = y gen i) := by
  induction t with
  | zero => simp
  | succ t ih =>
      rcases ih with ⟨hx, hq, ha, hy⟩
      constructor
      · intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simp [run, step, x, extendPresentation]
        · simpa [run, step, x, extendPresentation] using hx j
      constructor
      · intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simp [run, step, q]
        · simpa [run, step, q] using hq j
      constructor
      · intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simp [run, step, a]
        · simpa [run, step, a] using ha j
      · intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simp [run, step, y]
        · simpa [run, step, y] using hy j


private lemma x_even (gen : FeedbackGenerator) (r : ℕ) : x gen (2 * r) = 2 ^ r := by
  simp [x, choosePresentation, even_two_mul]

private lemma freshCandidate_form {t : ℕ} (s : SimState t) :
    ∃ i < 3 * t + 1, freshCandidate s = 2 * i + 3 := by
  obtain ⟨i, hi, heq⟩ := by simpa [candidates] using freshCandidate_mem s
  exact ⟨i, hi, heq.symm⟩

private lemma freshCandidate_bound {t : ℕ} (s : SimState t) :
    freshCandidate s ≤ 6 * t + 3 := by
  obtain ⟨i, hi, heq⟩ := freshCandidate_form s
  rw [heq]
  omega

private lemma oddCandidate_not_core (i : ℕ) : 2 * i + 3 ∉ core := by
  rintro ⟨k, hk⟩
  cases k with
  | zero => simp at hk
  | succ k =>
      simp [pow_succ] at hk
      omega

private lemma freshCandidate_not_core {t : ℕ} (s : SimState t) : freshCandidate s ∉ core := by
  obtain ⟨i, -, hi⟩ := freshCandidate_form s
  rw [hi]
  exact oddCandidate_not_core i

private lemma x_odd_not_core (gen : FeedbackGenerator) {t : ℕ} (ht : ¬ Even t) : x gen t ∉ core := by
  simp [x, choosePresentation, ht, freshCandidate_not_core]

private lemma x_odd_bound (gen : FeedbackGenerator) {t : ℕ} (ht : ¬ Even t) :
    x gen t ≤ 6 * t + 3 := by
  simpa [x, choosePresentation, ht] using freshCandidate_bound (run gen t)

private lemma freshCandidate_ne_presentation {t : ℕ} (s : SimState t) (i : Fin t) :
    freshCandidate s ≠ s.presentation i := by
  intro h
  apply freshCandidate_not_forbidden s
  simp [forbidden, h]

private lemma freshCandidate_ne_query {t : ℕ} (s : SimState t) (i : Fin t) (z : ℕ)
    (hi : s.query i = some z) : freshCandidate s ≠ z := by
  intro h
  apply freshCandidate_not_forbidden s
  simp only [forbidden, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
  exact Or.inl (Or.inr ⟨i, by simp [hi, h]⟩)

private lemma freshCandidate_ne_output {t : ℕ} (s : SimState t) (i : Fin t) :
    freshCandidate s ≠ s.output i := by
  intro h
  apply freshCandidate_not_forbidden s
  simp [forbidden, h]

private lemma x_odd_ne_prior_x (gen : FeedbackGenerator) {t : ℕ} (ht : ¬ Even t)
    {i : ℕ} (hi : i < t) : x gen t ≠ x gen i := by
  have hh := (run_history gen t).1 ⟨i, hi⟩
  simpa [x, choosePresentation, ht, hh] using
    freshCandidate_ne_presentation (run gen t) ⟨i, hi⟩

private lemma x_odd_ne_prior_q (gen : FeedbackGenerator) {t : ℕ} (ht : ¬ Even t)
    {i z : ℕ} (hi : i < t) (hq : q gen i = some z) : x gen t ≠ z := by
  have hh := (run_history gen t).2.1 ⟨i, hi⟩
  simpa [x, choosePresentation, ht] using
    (freshCandidate_ne_query (run gen t) ⟨i, hi⟩ z (by simpa [hh] using hq))

private lemma x_odd_ne_prior_y (gen : FeedbackGenerator) {t : ℕ} (ht : ¬ Even t)
    {i : ℕ} (hi : i < t) : x gen t ≠ y gen i := by
  have hh := (run_history gen t).2.2.2 ⟨i, hi⟩
  simpa [x, choosePresentation, ht, hh] using
    freshCandidate_ne_output (run gen t) ⟨i, hi⟩

private lemma x_ne_of_lt (gen : FeedbackGenerator) {m n : ℕ} (hlt : m < n) :
    x gen m ≠ x gen n := by
  by_cases hn : Even n
  · obtain ⟨r, rfl⟩ := even_iff_exists_two_mul.mp hn
    by_cases hm : Even m
    · obtain ⟨s, rfl⟩ := even_iff_exists_two_mul.mp hm
      rw [x_even, x_even]
      intro heq
      have : s = r := Nat.pow_right_injective (by omega) heq
      omega
    · rw [x_even]
      intro heq
      exact x_odd_not_core gen hm ⟨r, heq.symm⟩
  · exact fun heq => (x_odd_ne_prior_x gen hn hlt) heq.symm

private lemma x_injective (gen : FeedbackGenerator) : Function.Injective (x gen) := by
  intro m n hmn
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact x_ne_of_lt gen hlt hmn
  · exact x_ne_of_lt gen hgt hmn.symm


private def K (gen : FeedbackGenerator) : Language := Set.range (x gen)

private lemma core_subset_K (gen : FeedbackGenerator) : core ⊆ K gen := by
  rintro z ⟨r, rfl⟩
  exact ⟨2 * r, x_even gen r⟩

private lemma K_infinite (gen : FeedbackGenerator) : (K gen).Infinite :=
  Set.infinite_range_of_injective (x_injective gen)

private lemma K_mem_targetClass (gen : FeedbackGenerator) : K gen ∈ targetClass := by
  refine ⟨K gen ∩ ordinary, inter_subset_right, ?_⟩
  ext z
  constructor
  · intro hz
    by_cases hc : z ∈ core
    · exact Or.inl hc
    · exact Or.inr ⟨hz, hc⟩
  · intro hz
    rcases hz with hc | hzK
    · exact core_subset_K gen hc
    · exact hzK.1

private noncomputable def tr (gen : FeedbackGenerator) : Transcript := {
  presentation := x gen
  query := q gen
  answer := a gen
  output := y gen
}

private noncomputable def presenter (gen : FeedbackGenerator) : CausalPresenter := {
  next := fun t _ _ _ _ => x gen t
}

private lemma presentedBy (gen : FeedbackGenerator) : PresentedBy (presenter gen) (tr gen) := by
  intro t
  rfl

private lemma mem_K_of_query (gen : FeedbackGenerator) {t z : ℕ} (hq : q gen t = some z) :
    z ∈ K gen ↔ z ∈ core ∪ Set.range (extendPresentation (run gen t)) := by
  constructor
  · rintro ⟨s, rfl⟩
    by_cases hs : s < t
    · right
      refine ⟨Fin.castSucc ⟨s, hs⟩, ?_⟩
      have hh := (run_history gen t).1 ⟨s, hs⟩
      simp only [extendPresentation, Fin.snoc_castSucc, hh]
    · by_cases hst : s = t
      · subst s
        right
        exact ⟨Fin.last t, by simp [extendPresentation, x]⟩
      · have hts : t < s := lt_of_le_of_ne (Nat.le_of_not_gt hs) (Ne.symm hst)
        by_cases he : Even s
        · obtain ⟨r, rfl⟩ := even_iff_exists_two_mul.mp he
          left
          exact ⟨r, (x_even gen r).symm⟩
        · exfalso
          exact (x_odd_ne_prior_q gen he hts hq) rfl
  · rintro (hc | hp)
    · exact core_subset_K gen hc
    · rcases hp with ⟨i, rfl⟩
      exact ⟨i, by
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simp [extendPresentation, x]
        · have hh := (run_history gen t).1 j
          simpa [extendPresentation, hh]⟩

private lemma followsProtocol (gen : FeedbackGenerator) : FollowsProtocol gen (K gen) (tr gen) := by
  intro t
  have hist := run_history gen t
  have histx : (fun i : Fin (t + 1) => x gen i) = extendPresentation (run gen t) := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [extendPresentation, x]
    · simpa [extendPresentation] using (hist.1 j).symm
  have hista : (fun i : Fin t => a gen i) = (run gen t).answer := by
    funext i
    exact (hist.2.2.1 i).symm
  have hquery : q gen t = gen.query t (fun i => x gen i) (fun i => a gen i) := by
    simp [q, makeRound, histx, hista]
  have hanswer : a gen t = match q gen t with
      | none => none
      | some z => some (membershipAnswer (K gen) z) := by
    change (makeRound gen (run gen t)).2.1 = match (makeRound gen (run gen t)).1 with
      | none => none
      | some z => some (membershipAnswer (K gen) z)
    simp only [makeRound]
    generalize hq0 : gen.query t (extendPresentation (run gen t)) (run gen t).answer = oq
    cases oq with
    | none => simp
    | some z =>
        simp only
        have hqt : q gen t = some z := by
          unfold q
          simp only [makeRound]
          exact hq0
        have hp := (mem_K_of_query gen hqt).symm
        have heq : (z ∈ core ∪ Set.range (extendPresentation (run gen t))) = (z ∈ K gen) :=
          propext hp
        congr 1
        unfold membershipAnswer
        rw [heq]
  have histap : (fun i : Fin (t + 1) => a gen i) =
      Fin.snoc (α := fun _ => Option Bool) (run gen t).answer (a gen t) := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp
    · simpa using (hist.2.2.1 j).symm
  refine ⟨hquery, hanswer, ?_⟩
  change y gen t = gen.output t (fun i => x gen i) (fun i => a gen i)
  unfold y
  simp only [makeRound]
  rw [histx, histap]
  congr 2

private lemma clean (gen : FeedbackGenerator) : Clean (x gen) (K gen) :=
  fun t => ⟨t, rfl⟩

private lemma complete (gen : FeedbackGenerator) : Complete (x gen) (K gen) := by
  rintro z ⟨t, rfl⟩
  exact ⟨t, rfl⟩

private lemma scored_subset_core (gen : FeedbackGenerator) :
    scored (K gen) (x gen) (y gen) ⊆ core := by
  intro z hz
  rcases hz with ⟨⟨s, hs⟩, t, hyt, hobs⟩
  subst z
  by_contra hcore
  have hsodd : ¬ Even s := by
    intro he
    obtain ⟨r, rfl⟩ := even_iff_exists_two_mul.mp he
    apply hcore
    exact ⟨r, (x_even gen r).symm⟩
  have hts : t < s := by
    by_contra hnot
    apply hobs
    exact ⟨s, Nat.le_of_not_gt hnot, rfl⟩
  exact (x_odd_ne_prior_y gen hsodd hts) hyt.symm

open Stage3S2B
lemma sq_le_two_pow_succ (k : ℕ) : k * k ≤ 2 ^ (k + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ]
      by_cases hk : k ≤ 2
      · have hcases : k = 0 ∨ k = 1 ∨ k = 2 := by omega
        rcases hcases with rfl | rfl | rfl <;> norm_num
      · have hk2 : 2 * k + 1 ≤ k * k := by nlinarith
        calc
          (k + 1) * (k + 1) ≤ 2 * (k * k) := by nlinarith
          _ ≤ 2 * 2 ^ (k + 1) := Nat.mul_le_mul_left 2 ih
          _ = 2 ^ (k + 1) * 2 := Nat.mul_comm _ _

noncomputable def coreExponent (z : ℕ) : ℕ := by
  classical
  exact if hz : z ∈ core then Classical.choose hz else 0

lemma pow_coreExponent {z : ℕ} (hz : z ∈ core) : 2 ^ coreExponent z = z := by
  classical
  simp only [coreExponent, dif_pos hz]
  exact Classical.choose_spec hz

lemma coreExponent_injOn : Set.InjOn coreExponent core := by
  intro z hz w hw he
  rw [← pow_coreExponent hz, ← pow_coreExponent hw, he]

noncomputable def coreCount (M : ℕ) : ℕ := by
  classical
  exact Nat.count (fun z => z ∈ core) (M + 1)

lemma count_core_le_sqrt (M : ℕ) :
    coreCount M ≤ Nat.sqrt (2 * M) + 1 := by
  classical
  rw [coreCount, Nat.count_eq_card_filter_range]
  let s := (Finset.range (M + 1)).filter (fun z => z ∈ core)
  have hcard : (s.image coreExponent).card = s.card := by
    rw [Finset.card_image_iff]
    intro z hz w hw he
    have hz' : z < M + 1 ∧ z ∈ core := by simpa [s] using hz
    have hw' : w < M + 1 ∧ w ∈ core := by simpa [s] using hw
    exact coreExponent_injOn hz'.2 hw'.2 he
  rw [← hcard]
  calc
    (s.image coreExponent).card ≤ (Finset.range (Nat.sqrt (2 * M) + 1)).card := by
      apply Finset.card_le_card
      rw [Finset.image_subset_iff]
      intro z hz
      simp only [Finset.mem_range]
      have hz' : z < M + 1 ∧ z ∈ core := by simpa [s] using hz
      have hsq : coreExponent z * coreExponent z ≤ 2 * M := by
        calc
          coreExponent z * coreExponent z ≤ 2 ^ (coreExponent z + 1) := sq_le_two_pow_succ _
          _ = 2 * z := by rw [pow_succ, pow_coreExponent hz'.2]; omega
          _ ≤ 2 * M := by omega
      exact Nat.lt_succ_iff.mpr (Nat.le_sqrt.mpr hsq)
    _ = Nat.sqrt (2 * M) + 1 := Finset.card_range _

private noncomputable def enumK (gen : FeedbackGenerator) : ℕ → ℕ :=
  Nat.nth (fun z => z ∈ K gen)

private lemma enumK_strictMono (gen : FeedbackGenerator) : StrictMono (enumK gen) :=
  Nat.nth_strictMono (K_infinite gen)

private lemma range_enumK (gen : FeedbackGenerator) : Set.range (enumK gen) = K gen :=
  Nat.range_nth_of_infinite (K_infinite gen)

private lemma enumK_bound (gen : FeedbackGenerator) (n : ℕ) :
    enumK gen n ≤ 12 * n + 9 := by
  classical
  let f : ℕ → ℕ := fun r => x gen (2 * r + 1)
  let s := (Finset.range (n + 1)).image f
  have hf : Function.Injective f := (x_injective gen).comp (by
    intro r u h
    simp only [f] at h
    omega)
  have hcard : s.card = n + 1 := by
    simp [s, Finset.card_image_of_injective _ hf]
  have hsub : s ⊆ (Finset.range (12 * n + 9 + 1)).filter (fun z => z ∈ K gen) := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨r, hr, rfl⟩
    have hrn : r ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
    have hodd : ¬Even (2 * r + 1) := by
      rintro ⟨u, hu⟩
      omega
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_range.mpr
      have hxbound := x_odd_bound gen hodd
      simp only [f]
      omega
    · exact ⟨2 * r + 1, rfl⟩
  apply Nat.lt_succ_iff.mp
  apply Nat.nth_lt_of_lt_count
  rw [Nat.count_eq_card_filter_range]
  calc
    n < n + 1 := Nat.lt_succ_self n
    _ = s.card := hcard.symm
    _ ≤ ((Finset.range (12 * n + 9 + 1)).filter (fun z => z ∈ K gen)).card :=
      Finset.card_le_card hsub

private noncomputable def orderedK (gen : FeedbackGenerator) : OrderedLanguage := {
  carrier := K gen
  enumeration := enumK gen
  enumeration_injective := (enumK_strictMono gen).injective
  range_enumeration := range_enumK gen
}

private lemma orderedK_inherits (gen : FeedbackGenerator) : InheritsAmbientOrder (orderedK gen) :=
  enumK_strictMono gen


private lemma prefixCount_core_le (gen : FeedbackGenerator) (n : ℕ) :
    (orderedK gen).prefixCount core n ≤ coreCount (12 * n + 9) := by
  classical
  unfold GenLimit.KleinbergWei.OrderedLanguage.prefixCount coreCount
  rw [Nat.count_eq_card_filter_range]
  let s := (Finset.range n).filter (fun i => enumK gen i ∈ core)
  have hcard : (s.image (enumK gen)).card = s.card := by
    rw [Finset.card_image_iff]
    exact (enumK_strictMono gen).injective.injOn
  change s.card ≤ ((Finset.range (12 * n + 9 + 1)).filter (fun z => z ∈ core)).card
  rw [← hcard]
  apply Finset.card_le_card
  rw [Finset.image_subset_iff]
  intro i hi
  have hi' : i < n ∧ enumK gen i ∈ core := by simpa [s] using hi
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_range.mpr (by
    have hib := enumK_bound gen i
    omega), hi'.2⟩

private lemma prefixCount_scored_le (gen : FeedbackGenerator) (n : ℕ) :
    (orderedK gen).prefixCount (scored (K gen) (x gen) (y gen)) n ≤
      (orderedK gen).prefixCount core n := by
  classical
  unfold GenLimit.KleinbergWei.OrderedLanguage.prefixCount
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢
  exact ⟨hi.1, scored_subset_core gen hi.2⟩


private lemma prefixCount_scored_bound (gen : FeedbackGenerator) (n : ℕ) :
    (orderedK gen).prefixCount (scored (K gen) (x gen) (y gen)) n ≤
      Nat.sqrt (2 * (12 * n + 9)) + 1 := by
  exact (prefixCount_scored_le gen n).trans
    ((prefixCount_core_le gen n).trans (count_core_le_sqrt (12 * n + 9)))

private noncomputable def densityBound (n : ℕ) : ℝ :=
  √42 * √(1 / (n : ℝ)) + 1 / (n : ℝ)

private lemma prefixRatio_scored_le_densityBound (gen : FeedbackGenerator) (n : ℕ) :
    (orderedK gen).prefixRatio (scored (K gen) (x gen) (y gen)) n ≤ densityBound n := by
  by_cases hn : n = 0
  · subst n
    simp [GenLimit.KleinbergWei.OrderedLanguage.prefixRatio, densityBound]
  have hnpos : 0 < (n : ℝ) := by positivity
  have hcountReal :
      ((orderedK gen).prefixCount (scored (K gen) (x gen) (y gen)) n : ℝ) ≤
        √(((2 * (12 * n + 9) : ℕ) : ℝ)) + 1 := by
    calc
      ((orderedK gen).prefixCount (scored (K gen) (x gen) (y gen)) n : ℝ)
          ≤ ((Nat.sqrt (2 * (12 * n + 9)) + 1 : ℕ) : ℝ) := by
            exact_mod_cast prefixCount_scored_bound gen n
      _ = (Nat.sqrt (2 * (12 * n + 9)) : ℝ) + 1 := by norm_num
      _ ≤ √(((2 * (12 * n + 9) : ℕ) : ℝ)) + 1 :=
        add_le_add_right Real.nat_sqrt_le_real_sqrt 1
  have hrad : (((2 * (12 * n + 9) : ℕ) : ℝ)) ≤ 42 * (n : ℝ) := by
    push_cast
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    nlinarith
  have hsqrtdiv :
      √(((2 * (12 * n + 9) : ℕ) : ℝ)) / (n : ℝ) ≤
        √42 * √(1 / (n : ℝ)) := by
    calc
      √(((2 * (12 * n + 9) : ℕ) : ℝ)) / (n : ℝ)
          ≤ √(42 * (n : ℝ)) / (n : ℝ) :=
            div_le_div_of_nonneg_right (Real.sqrt_le_sqrt hrad) hnpos.le
      _ = √42 * √(n : ℝ) / (n : ℝ) := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 42)]
      _ = √42 * (√(n : ℝ) / (n : ℝ)) := by ring
      _ = √42 * √(1 / (n : ℝ)) := by
        rw [Real.sqrt_div_self, one_div, Real.sqrt_inv]
  rw [GenLimit.KleinbergWei.OrderedLanguage.prefixRatio, if_neg hn]
  calc
    ((orderedK gen).prefixCount (scored (K gen) (x gen) (y gen)) n : ℝ) / (n : ℝ)
        ≤ (√(((2 * (12 * n + 9) : ℕ) : ℝ)) + 1) / (n : ℝ) :=
          div_le_div_of_nonneg_right hcountReal hnpos.le
    _ = √(((2 * (12 * n + 9) : ℕ) : ℝ)) / (n : ℝ) + 1 / (n : ℝ) := by ring
    _ ≤ √42 * √(1 / (n : ℝ)) + 1 / (n : ℝ) := add_le_add_right hsqrtdiv _
    _ = densityBound n := rfl

private lemma tendsto_one_div_nat :
    Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
  exact tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop

private lemma densityBound_tendsto_zero : Tendsto densityBound atTop (𝓝 0) := by
  have hsqrt : Tendsto (fun n : ℕ => √(1 / (n : ℝ))) atTop (𝓝 0) := by
    simpa only [Real.sqrt_zero] using tendsto_one_div_nat.sqrt
  have hmul : Tendsto (fun n : ℕ => √42 * √(1 / (n : ℝ))) atTop (𝓝 0) := by
    convert tendsto_const_nhds.mul hsqrt using 1 <;> norm_num
  unfold densityBound
  convert hmul.add tendsto_one_div_nat using 1 <;> norm_num

private lemma prefixRatio_scored_nonneg (gen : FeedbackGenerator) (n : ℕ) :
    0 ≤ (orderedK gen).prefixRatio (scored (K gen) (x gen) (y gen)) n := by
  unfold GenLimit.KleinbergWei.OrderedLanguage.prefixRatio
  split_ifs
  · exact le_rfl
  · positivity

private lemma prefixRatio_scored_tendsto_zero (gen : FeedbackGenerator) :
    Tendsto ((orderedK gen).prefixRatio (scored (K gen) (x gen) (y gen))) atTop (𝓝 0) := by
  exact squeeze_zero (prefixRatio_scored_nonneg gen) (prefixRatio_scored_le_densityBound gen)
    densityBound_tendsto_zero

private lemma upperDensity_scored_eq_zero (gen : FeedbackGenerator) :
    (orderedK gen).upperDensity (scored (K gen) (x gen) (y gen)) = 0 := by
  exact (prefixRatio_scored_tendsto_zero gen).limsup_eq


private noncomputable def encodedTarget (S : Set ℕ) : {K : Language // K ∈ targetClass} := by
  refine ⟨core ∪ (fun n : ℕ => 2 * n + 3) '' S, ?_⟩
  refine ⟨(fun n : ℕ => 2 * n + 3) '' S, ?_, rfl⟩
  intro z hz
  rcases hz with ⟨n, -, rfl⟩
  exact oddCandidate_not_core n

private lemma encodedTarget_injective : Function.Injective encodedTarget := by
  intro S T hST
  apply Set.ext
  intro n
  have hu : (encodedTarget S : Language) = encodedTarget T := congrArg Subtype.val hST
  have hncore : 2 * n + 3 ∉ core := oddCandidate_not_core n
  constructor
  · intro hnS
    have hzS : 2 * n + 3 ∈ (encodedTarget S : Language) := by
      exact Or.inr ⟨n, hnS, rfl⟩
    have hzT : 2 * n + 3 ∈ (encodedTarget T : Language) := hu ▸ hzS
    rcases hzT with hzcore | ⟨m, hmT, hmn⟩
    · exact False.elim (hncore hzcore)
    · exact (candidate_map_injective hmn).symm ▸ hmT
  · intro hnT
    have hzT : 2 * n + 3 ∈ (encodedTarget T : Language) := by
      exact Or.inr ⟨n, hnT, rfl⟩
    have hzS : 2 * n + 3 ∈ (encodedTarget S : Language) := hu.symm ▸ hzT
    rcases hzS with hzcore | ⟨m, hmS, hmn⟩
    · exact False.elim (hncore hzcore)
    · exact (candidate_map_injective hmn).symm ▸ hmS

private lemma targetClass_not_countable : ¬ targetClass.Countable := by
  intro hcount
  letI : Countable {K : Language // K ∈ targetClass} := Set.countable_coe_iff.mpr hcount
  letI : Countable (Set ℕ) := encodedTarget_injective.countable
  obtain ⟨f, hf⟩ := Countable.exists_injective_nat (Set ℕ)
  exact Function.cantor_injective f hf

private lemma positiveClaim : UniformlyGeneratableWithoutSamples := by
  refine ⟨fun t : ℕ => 2 ^ t, ?_, 0, ?_⟩
  · exact Nat.pow_right_injective (by omega)
  · intro K hK t _
    rcases hK with ⟨A, hA, rfl⟩
    exact Or.inl ⟨t, rfl⟩

private lemma negativeClaim : NegativeClaim := by
  intro gen _
  refine ⟨K gen, K_mem_targetClass gen, presenter gen, tr gen, orderedK gen, ?_⟩
  exact ⟨rfl, orderedK_inherits gen, presentedBy gen, followsProtocol gen,
    clean gen, x_injective gen, complete gen, upperDensity_scored_eq_zero gen⟩

lemma mainClaim : MainClaim :=
  ⟨targetClass_not_countable, positiveClaim, negativeClaim⟩

end Stage3Proof

theorem stage3_result : Stage3S2B.MainClaim := Stage3Proof.mainClaim
