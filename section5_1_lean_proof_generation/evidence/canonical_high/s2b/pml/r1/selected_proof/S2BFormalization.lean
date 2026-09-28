import Stage3Model
import GenLimit.Paper10_UnionClosednessOfLanguageGeneration.Cardinality
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.Sqrt
import GenLimit.Paper17_InfiniteContamination.SharedVanishingPresentation
import Mathlib.Tactic.IntervalCases

open Filter
open scoped Topology

namespace S2BProof

open Stage3S2B

noncomputable section

def oddCode (n : ℕ) : ℕ := 2 * n + 3

theorem oddCode_injective : Function.Injective oddCode := by
  intro a b h
  simp only [oddCode] at h
  omega

theorem oddCode_mem_ordinary (n : ℕ) : oddCode n ∈ ordinary := by
  intro hcore
  obtain ⟨k, hk⟩ := hcore
  cases k with
  | zero => simp [oddCode] at hk
  | succ k =>
      simp only [oddCode, pow_succ] at hk
      omega

theorem ordinary_infinite : ordinary.Infinite := by
  exact (Set.infinite_range_of_injective oddCode_injective).mono
    (by rintro _ ⟨n, rfl⟩; exact oddCode_mem_ordinary n)

def forbidden {t : ℕ} (x : Fin t → ℕ) (q : Fin t → Option ℕ)
    (y : Fin t → ℕ) : Finset ℕ :=
  (Finset.univ.image x ∪ Finset.univ.image y) ∪
    Finset.univ.image (fun i => (q i).getD 0)

theorem forbidden_card_le {t : ℕ} (x : Fin t → ℕ)
    (q : Fin t → Option ℕ) (y : Fin t → ℕ) :
    (forbidden x q y).card ≤ 3 * t := by
  classical
  unfold forbidden
  let A := Finset.univ.image x
  let B := Finset.univ.image y
  let C := Finset.univ.image (fun i => (q i).getD 0)
  have hA : A.card ≤ t := by
    simpa [A] using
      (Finset.card_image_le : (Finset.univ.image x).card ≤ (Finset.univ : Finset (Fin t)).card)
  have hB : B.card ≤ t := by
    simpa [B] using
      (Finset.card_image_le : (Finset.univ.image y).card ≤ (Finset.univ : Finset (Fin t)).card)
  have hC : C.card ≤ t := by
    simpa [C] using
      (Finset.card_image_le :
        (Finset.univ.image (fun i => (q i).getD 0)).card ≤
          (Finset.univ : Finset (Fin t)).card)
  calc
    ((A ∪ B) ∪ C).card ≤ (A ∪ B).card + C.card :=
      Finset.card_union_le (A ∪ B) C
    _ ≤ (A.card + B.card) + C.card :=
      Nat.add_le_add_right (Finset.card_union_le A B) _
    _ ≤ t + t + t := by
      exact Nat.add_le_add (Nat.add_le_add hA hB) hC
    _ = 3 * t := by omega

theorem available_exists {t : ℕ} (x : Fin t → ℕ)
    (q : Fin t → Option ℕ) (y : Fin t → ℕ) :
    ∃ z, z ∈ ordinary ∧ z ∉ forbidden x q y := by
  obtain ⟨z, hz, hzf⟩ := ordinary_infinite.exists_notMem_finset (forbidden x q y)
  exact ⟨z, hz, hzf⟩

def choosePresentation (t : ℕ) (x : Fin t → ℕ)
    (q : Fin t → Option ℕ) (y : Fin t → ℕ) : ℕ :=
  by
    classical
    exact if Even t then 2 ^ (t / 2) else Nat.find (available_exists x q y)

theorem choosePresentation_even {t : ℕ} (x : Fin t → ℕ)
    (q : Fin t → Option ℕ) (y : Fin t → ℕ) (ht : Even t) :
    choosePresentation t x q y = 2 ^ (t / 2) := by
  simp [choosePresentation, ht]

theorem choosePresentation_odd_mem {t : ℕ} (x : Fin t → ℕ)
    (q : Fin t → Option ℕ) (y : Fin t → ℕ) (ht : ¬ Even t) :
    choosePresentation t x q y ∈ ordinary := by
  classical
  simp only [choosePresentation, if_neg ht]
  exact (Nat.find_spec (available_exists x q y)).1

theorem choosePresentation_odd_not_forbidden {t : ℕ} (x : Fin t → ℕ)
    (q : Fin t → Option ℕ) (y : Fin t → ℕ) (ht : ¬ Even t) :
    choosePresentation t x q y ∉ forbidden x q y := by
  classical
  simp only [choosePresentation, if_neg ht]
  exact (Nat.find_spec (available_exists x q y)).2

def committed {t : ℕ} (x : Fin t → ℕ) : Language :=
  core ∪ {z | ∃ i : Fin t, Odd i.val ∧ x i = z}

def answerNow {t : ℕ} (x : Fin t → ℕ) (q : Option ℕ) : Option Bool :=
  by
    classical
    exact q.map fun z => decide (z ∈ committed x)

structure History (t : ℕ) where
  presentation : Fin t → ℕ
  query : Fin t → Option ℕ
  answer : Fin t → Option Bool
  output : Fin t → ℕ

def extend {t : ℕ} {α : Type} (a : α) (f : Fin t → α) : Fin (t + 1) → α :=
  Fin.lastCases a f

def step (gen : FeedbackGenerator) {t : ℕ} (h : History t) : History (t + 1) :=
  let x := choosePresentation t h.presentation h.query h.output
  let xp := extend x h.presentation
  let q := gen.query t xp h.answer
  let a := answerNow xp q
  let ap := extend a h.answer
  let y := gen.output t xp ap
  { presentation := xp
    query := extend q h.query
    answer := ap
    output := extend y h.output }

def history (gen : FeedbackGenerator) : (t : ℕ) → History t
  | 0 =>
      { presentation := Fin.elim0
        query := Fin.elim0
        answer := Fin.elim0
        output := Fin.elim0 }
  | t + 1 => step gen (history gen t)

def presentation (gen : FeedbackGenerator) (t : ℕ) : ℕ :=
  (history gen (t + 1)).presentation (Fin.last t)

def query (gen : FeedbackGenerator) (t : ℕ) : Option ℕ :=
  (history gen (t + 1)).query (Fin.last t)

def answer (gen : FeedbackGenerator) (t : ℕ) : Option Bool :=
  (history gen (t + 1)).answer (Fin.last t)

def output (gen : FeedbackGenerator) (t : ℕ) : ℕ :=
  (history gen (t + 1)).output (Fin.last t)

def target (gen : FeedbackGenerator) : Language :=
  core ∪ {z | ∃ t, Odd t ∧ presentation gen t = z}

def transcript (gen : FeedbackGenerator) : Transcript where
  presentation := presentation gen
  query := query gen
  answer := answer gen
  output := output gen

@[simp] theorem extend_last {t : ℕ} {α : Type} (a : α) (f : Fin t → α) :
    extend a f (Fin.last t) = a := by
  simp [extend]

@[simp] theorem extend_castSucc {t : ℕ} {α : Type} (a : α)
    (f : Fin t → α) (i : Fin t) :
    extend a f i.castSucc = f i := by
  simp [extend]

theorem history_presentation_eq (gen : FeedbackGenerator) (t : ℕ) (i : Fin t) :
    (history gen t).presentation i = presentation gen i.val := by
  induction t with
  | zero => exact Fin.elim0 i
  | succ t ih =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rfl
      · simpa [history, step] using ih j

theorem history_query_eq (gen : FeedbackGenerator) (t : ℕ) (i : Fin t) :
    (history gen t).query i = query gen i.val := by
  induction t with
  | zero => exact Fin.elim0 i
  | succ t ih =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rfl
      · simpa [history, step] using ih j

theorem history_answer_eq (gen : FeedbackGenerator) (t : ℕ) (i : Fin t) :
    (history gen t).answer i = answer gen i.val := by
  induction t with
  | zero => exact Fin.elim0 i
  | succ t ih =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rfl
      · simpa [history, step] using ih j

theorem history_output_eq (gen : FeedbackGenerator) (t : ℕ) (i : Fin t) :
    (history gen t).output i = output gen i.val := by
  induction t with
  | zero => exact Fin.elim0 i
  | succ t ih =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rfl
      · simpa [history, step] using ih j

theorem presentation_eq_choose (gen : FeedbackGenerator) (t : ℕ) :
    presentation gen t = choosePresentation t
      (fun i => presentation gen i) (fun i => query gen i)
      (fun i => output gen i) := by
  rw [show presentation gen t = choosePresentation t
      (history gen t).presentation (history gen t).query
      (history gen t).output by simp [presentation, history, step]]
  congr 1 <;> funext i
  · exact history_presentation_eq gen t i
  · exact history_query_eq gen t i
  · exact history_output_eq gen t i

theorem query_eq_generator (gen : FeedbackGenerator) (t : ℕ) :
    query gen t = gen.query t (fun i => presentation gen i)
      (fun i => answer gen i) := by
  rw [show query gen t = gen.query t
      (history gen (t + 1)).presentation (history gen t).answer by
        simp [query, history, step]]
  congr 1 <;> funext i
  · exact history_presentation_eq gen (t + 1) i
  · exact history_answer_eq gen t i

theorem output_eq_generator (gen : FeedbackGenerator) (t : ℕ) :
    output gen t = gen.output t (fun i => presentation gen i)
      (fun i => answer gen i) := by
  rw [show output gen t = gen.output t
      (history gen (t + 1)).presentation
      (history gen (t + 1)).answer by
        simp [output, history, step]]
  congr 1 <;> funext i
  · exact history_presentation_eq gen (t + 1) i
  · exact history_answer_eq gen (t + 1) i

theorem presentation_even (gen : FeedbackGenerator) (r : ℕ) :
    presentation gen (2 * r) = 2 ^ r := by
  rw [presentation_eq_choose]
  rw [choosePresentation_even]
  · congr 1
    omega
  · exact ⟨r, by omega⟩

theorem presentation_odd_mem (gen : FeedbackGenerator) {t : ℕ} (ht : Odd t) :
    presentation gen t ∈ ordinary := by
  rw [presentation_eq_choose]
  exact choosePresentation_odd_mem _ _ _ (Nat.not_even_iff_odd.mpr ht)

theorem presentation_odd_not_forbidden (gen : FeedbackGenerator) {t : ℕ}
    (ht : Odd t) :
    presentation gen t ∉ forbidden (t := t)
      (fun i : Fin t => presentation gen i)
      (fun i : Fin t => query gen i) (fun i : Fin t => output gen i) := by
  rw [presentation_eq_choose]
  exact choosePresentation_odd_not_forbidden _ _ _
    (Nat.not_even_iff_odd.mpr ht)

theorem later_odd_ne_presentation (gen : FeedbackGenerator) {i t : ℕ}
    (hit : i < t) (ht : Odd t) : presentation gen t ≠ presentation gen i := by
  intro heq
  have hnot := presentation_odd_not_forbidden gen ht
  apply hnot
  simp only [forbidden, Finset.mem_union, Finset.mem_image, Finset.mem_univ,
    true_and]
  exact Or.inl (Or.inl ⟨⟨i, hit⟩, heq.symm⟩)

theorem later_odd_ne_output (gen : FeedbackGenerator) {i t : ℕ}
    (hit : i < t) (ht : Odd t) : presentation gen t ≠ output gen i := by
  intro heq
  have hnot := presentation_odd_not_forbidden gen ht
  apply hnot
  simp only [forbidden, Finset.mem_union, Finset.mem_image, Finset.mem_univ,
    true_and]
  exact Or.inl (Or.inr ⟨⟨i, hit⟩, heq.symm⟩)

theorem later_odd_ne_query (gen : FeedbackGenerator) {i t z : ℕ}
    (hit : i < t) (ht : Odd t) (hq : query gen i = some z) :
    presentation gen t ≠ z := by
  intro heq
  have hnot := presentation_odd_not_forbidden gen ht
  apply hnot
  simp only [forbidden, Finset.mem_union, Finset.mem_image, Finset.mem_univ,
    true_and]
  exact Or.inr ⟨⟨i, hit⟩, by simp [hq, heq]⟩

theorem answer_eq_now (gen : FeedbackGenerator) (t : ℕ) :
    answer gen t = answerNow (fun i : Fin (t + 1) => presentation gen i)
      (query gen t) := by
  rw [show answer gen t = answerNow
      (history gen (t + 1)).presentation (query gen t) by
        simp [answer, query, history, step]]
  congr 1
  funext i
  exact history_presentation_eq gen (t + 1) i

theorem committed_iff_target_at_query (gen : FeedbackGenerator) (t z : ℕ)
    (hq : query gen t = some z) :
    z ∈ committed (fun i : Fin (t + 1) => presentation gen i) ↔
      z ∈ target gen := by
  constructor
  · intro hz
    rcases hz with hz | ⟨i, hiOdd, hi⟩
    · exact Or.inl hz
    · exact Or.inr ⟨i, hiOdd, hi⟩
  · intro hz
    rcases hz with hz | ⟨s, hsOdd, hs⟩
    · exact Or.inl hz
    · by_cases hst : s < t + 1
      · exact Or.inr ⟨⟨s, hst⟩, hsOdd, hs⟩
      · have hts : t < s := by omega
        exfalso
        exact later_odd_ne_query gen hts hsOdd hq hs

theorem followsProtocol (gen : FeedbackGenerator) :
    FollowsProtocol gen (target gen) (transcript gen) := by
  classical
  intro t
  change query gen t = gen.query t _ _ ∧
    answer gen t = (match query gen t with
      | none => none
      | some z => some (membershipAnswer (target gen) z)) ∧
    output gen t = gen.output t _ _
  refine ⟨query_eq_generator gen t, ?_, output_eq_generator gen t⟩
  rw [answer_eq_now]
  cases hq : query gen t with
  | none => simp [answerNow, hq]
  | some z =>
      simp only [answerNow, hq, Option.map_some]
      unfold membershipAnswer
      rw [show (decide (z ∈ committed
        (fun i : Fin (t + 1) => presentation gen ↑i)) : Bool) =
          decide (z ∈ target gen) by
            congr 1
            exact propext (committed_iff_target_at_query gen t z hq)]

theorem target_mem_class (gen : FeedbackGenerator) : target gen ∈ targetClass := by
  refine ⟨{z | ∃ t, Odd t ∧ presentation gen t = z}, ?_, rfl⟩
  rintro z ⟨t, ht, rfl⟩
  exact presentation_odd_mem gen ht

theorem presentation_clean (gen : FeedbackGenerator) :
    Clean (presentation gen) (target gen) := by
  intro t
  rcases Nat.even_or_odd t with ht | ht
  · obtain ⟨r, hr⟩ := ht
    left
    refine ⟨r, ?_⟩
    rw [show t = 2 * r by omega, presentation_even]
  · exact Or.inr ⟨t, ht, rfl⟩

theorem presentation_injective (gen : FeedbackGenerator) :
    Function.Injective (presentation gen) := by
  intro m n hmn
  rcases Nat.even_or_odd m with hm | hm <;>
    rcases Nat.even_or_odd n with hn | hn
  · obtain ⟨r, hr⟩ := hm
    obtain ⟨s, hs⟩ := hn
    have hp : 2 ^ r = 2 ^ s := by
      simpa [show m = 2 * r by omega, show n = 2 * s by omega,
        presentation_even] using hmn
    have : r = s := Nat.pow_right_injective (by omega) hp
    omega
  · have hmcore : presentation gen m ∈ core := by
      obtain ⟨r, hr⟩ := hm
      refine ⟨r, ?_⟩
      rw [show m = 2 * r by omega, presentation_even]
    have hncore : presentation gen n ∈ core := by rwa [← hmn]
    exact (presentation_odd_mem gen hn hncore).elim
  · have hncore : presentation gen n ∈ core := by
      obtain ⟨r, hr⟩ := hn
      refine ⟨r, ?_⟩
      rw [show n = 2 * r by omega, presentation_even]
    exact (presentation_odd_mem gen hm (hmn ▸ hncore)).elim
  · rcases lt_trichotomy m n with hlt | heq | hgt
    · exact (later_odd_ne_presentation gen hlt hn hmn.symm).elim
    · exact heq
    · exact (later_odd_ne_presentation gen hgt hm hmn).elim

theorem presentation_complete (gen : FeedbackGenerator) :
    Complete (presentation gen) (target gen) := by
  intro z hz
  rcases hz with ⟨r, rfl⟩ | ⟨t, _ht, rfl⟩
  · exact ⟨2 * r, presentation_even gen r⟩
  · exact ⟨t, rfl⟩

theorem core_infinite : core.Infinite := by
  exact Set.infinite_range_of_injective (Nat.pow_right_injective (by omega : 2 ≤ 2))

theorem target_infinite (gen : FeedbackGenerator) : (target gen).Infinite := by
  exact core_infinite.mono (fun _ hz => Or.inl hz)

noncomputable def orderedTarget (gen : FeedbackGenerator) : OrderedLanguage where
  carrier := target gen
  enumeration := Nat.nth (fun z => z ∈ target gen)
  enumeration_injective := Nat.nth_injective (target_infinite gen)
  range_enumeration := Nat.range_nth_of_infinite (target_infinite gen)

theorem orderedTarget_inherits (gen : FeedbackGenerator) :
    InheritsAmbientOrder (orderedTarget gen) :=
  Nat.nth_strictMono (target_infinite gen)

theorem exists_oddCode_not_mem (s : Finset ℕ) :
    ∃ i ≤ s.card, oddCode i ∉ s := by
  by_contra h
  push_neg at h
  have hsub : (Finset.range (s.card + 1)).image oddCode ⊆ s := by
    intro z hz
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
    exact h i (by have := Finset.mem_range.mp hi; omega)
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ oddCode_injective,
    Finset.card_range] at hc
  omega

theorem choosePresentation_odd_le {t : ℕ} (x : Fin t → ℕ)
    (q : Fin t → Option ℕ) (y : Fin t → ℕ) (ht : ¬ Even t) :
    choosePresentation t x q y ≤ 6 * t + 3 := by
  classical
  obtain ⟨i, hi, hin⟩ := exists_oddCode_not_mem (forbidden x q y)
  have havail : oddCode i ∈ ordinary ∧ oddCode i ∉ forbidden x q y :=
    ⟨oddCode_mem_ordinary i, hin⟩
  rw [choosePresentation, if_neg ht]
  calc
    Nat.find (available_exists x q y) ≤ oddCode i :=
      Nat.find_min' (available_exists x q y) havail
    _ ≤ 2 * (forbidden x q y).card + 3 := by
      simp only [oddCode]
      omega
    _ ≤ 6 * t + 3 := by
      have hc := forbidden_card_le x q y
      omega

theorem presentation_odd_round_le (gen : FeedbackGenerator) (r : ℕ) :
    presentation gen (2 * r + 1) ≤ 12 * r + 9 := by
  rw [presentation_eq_choose]
  have hodd : ¬ Even (2 * r + 1) := Nat.not_even_iff_odd.mpr ⟨r, by omega⟩
  have h := choosePresentation_odd_le
    (fun i : Fin (2 * r + 1) => presentation gen i)
    (fun i : Fin (2 * r + 1) => query gen i)
    (fun i : Fin (2 * r + 1) => output gen i) hodd
  omega

theorem orderedTarget_nth_le (gen : FeedbackGenerator) (n : ℕ) :
    (orderedTarget gen).enumeration n ≤ 12 * n + 9 := by
  classical
  let f : ℕ → ℕ := fun r => presentation gen (2 * r + 1)
  let candidates := (Finset.range (n + 1)).image f
  let initial := (Finset.range (12 * n + 10)).filter
    (fun z => z ∈ target gen)
  have hsub : candidates ⊆ initial := by
    intro z hz
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hz
    have hrn : r ≤ n := by
      have := Finset.mem_range.mp hr
      omega
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr ?_, Or.inr ?_⟩
    · dsimp [f]
      have hb := presentation_odd_round_le gen r
      omega
    · exact ⟨2 * r + 1, ⟨r, by omega⟩, rfl⟩
  have hfinj : Function.Injective f := by
    intro a b hab
    have := presentation_injective gen hab
    omega
  have hcard : n + 1 ≤ initial.card := by
    calc
      n + 1 = candidates.card := by
        simp [candidates, Finset.card_image_of_injective _ hfinj]
      _ ≤ initial.card := Finset.card_le_card hsub
  have hcount : n < Nat.count (fun z => z ∈ target gen) (12 * n + 10) := by
    rw [Nat.count_eq_card_filter_range]
    simpa [initial] using hcard
  exact Nat.le_of_lt_succ (by
    simpa [orderedTarget] using
      (Nat.nth_lt_of_lt_count (p := fun z => z ∈ target gen) hcount))

theorem square_le_two_pow_succ (k : ℕ) : k * k ≤ 2 ^ (k + 1) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
      by_cases hk : k ≤ 2
      · interval_cases k <;> norm_num
      · calc
          (k + 1) * (k + 1) ≤ 2 * (k * k) := by nlinarith
          _ ≤ 2 * 2 ^ (k + 1) := Nat.mul_le_mul_left 2 ih
          _ = 2 ^ ((k + 1) + 1) := by simp [pow_succ, mul_comm]

theorem sqrt_scaled_le (n : ℕ) :
    Nat.sqrt (26 * n) ≤ 26 * Nat.sqrt n + 26 := by
  apply Nat.le_of_lt_succ
  rw [Nat.sqrt_lt]
  have hn := Nat.lt_succ_sqrt n
  nlinarith

noncomputable def coreExponent (z : ℕ) : ℕ :=
  by
    classical
    exact if hz : z ∈ core then Nat.find hz else 0

theorem pow_coreExponent {z : ℕ} (hz : z ∈ core) :
    2 ^ coreExponent z = z := by
  classical
  simp only [coreExponent, dif_pos hz]
  exact Nat.find_spec hz

theorem coreExponent_injOn : Set.InjOn coreExponent core := by
  intro a ha b hb hab
  have hp : 2 ^ coreExponent a = 2 ^ coreExponent b := by rw [hab]
  rw [pow_coreExponent ha, pow_coreExponent hb] at hp
  exact hp

theorem prefixCount_core_le (gen : FeedbackGenerator) {n : ℕ} (hn : 9 ≤ n) :
    (orderedTarget gen).prefixCount core n ≤ Nat.sqrt (26 * n) + 1 := by
  classical
  let S := (Finset.range n).filter
    (fun i => (orderedTarget gen).enumeration i ∈ core)
  let e : ℕ → ℕ := fun i => coreExponent ((orderedTarget gen).enumeration i)
  have hinj : Set.InjOn e (S : Set ℕ) := by
    intro i hi j hj hij
    apply (orderedTarget gen).enumeration_injective
    apply coreExponent_injOn
    · exact (Finset.mem_filter.mp hi).2
    · exact (Finset.mem_filter.mp hj).2
    · exact hij
  have hsub : S.image e ⊆ Finset.range (Nat.sqrt (26 * n) + 1) := by
    intro k hk
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hk
    have hiRange := (Finset.mem_filter.mp hi).1
    have hiCore := (Finset.mem_filter.mp hi).2
    rw [Finset.mem_range]
    apply Nat.lt_succ_of_le
    rw [Nat.le_sqrt]
    have hp := square_le_two_pow_succ (coreExponent ((orderedTarget gen).enumeration i))
    have heq := pow_coreExponent hiCore
    have henum : (orderedTarget gen).enumeration i ≤
        (orderedTarget gen).enumeration n :=
      (orderedTarget_inherits gen).monotone (Nat.le_of_lt (Finset.mem_range.mp hiRange))
    have hbound := orderedTarget_nth_le gen n
    rw [pow_succ, heq] at hp
    nlinarith
  unfold GenLimit.KleinbergWei.OrderedLanguage.prefixCount
  change S.card ≤ _
  rw [← Finset.card_image_iff.mpr hinj]
  exact (Finset.card_le_card hsub).trans (by simp)

theorem tendsto_core_bound :
    Tendsto (fun n : ℕ => ((Nat.sqrt (26 * n) : ℝ) + 1) / (n : ℝ))
      atTop (𝓝 0) := by
  have hs := GenLimit.InfiniteContamination.tendsto_sparseSqrt_add_one_div
  have hi : Tendsto (fun n : ℕ => ((n : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inverse_atTop_nhds_zero_nat
  have hsum := (hs.const_mul (26 : ℝ)).add hi
  apply squeeze_zero
    (g := fun n : ℕ =>
      26 * (((Nat.sqrt n : ℝ) + 1) / (n : ℝ)) + ((n : ℝ))⁻¹)
  · intro n
    positivity
  · intro n
    by_cases hn0 : n = 0
    · simp [hn0]
    have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
    have h26 : (Nat.sqrt (26 * n) : ℝ) + 1 ≤
        26 * ((Nat.sqrt n : ℝ) + 1) + 1 := by
      exact_mod_cast Nat.add_le_add_right (sqrt_scaled_le n) 1
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    have hdiv := div_le_div_of_nonneg_right h26 hnpos.le
    rw [div_eq_mul_inv] at hdiv ⊢
    ring_nf at hdiv ⊢
    exact hdiv
  · simpa using hsum

theorem tendsto_prefixRatio_core (gen : FeedbackGenerator) :
    Tendsto ((orderedTarget gen).prefixRatio core) atTop (𝓝 0) := by
  apply squeeze_zero
    (fun n => (orderedTarget gen).prefixRatio_nonneg core n)
    ?_ tendsto_core_bound
  intro n
  by_cases hn0 : n = 0
  · simp [hn0]
  by_cases hn : 9 ≤ n
  · simp only [GenLimit.KleinbergWei.OrderedLanguage.prefixRatio, hn0, if_false]
    apply div_le_div_of_nonneg_right
    · exact_mod_cast prefixCount_core_le gen hn
    · positivity
  · have hnsmall : n ≤ 8 := by omega
    have hsqrt : n ≤ Nat.sqrt (26 * n) + 1 := by
      have haux : n - 1 ≤ Nat.sqrt (26 * n) := by
        rw [Nat.le_sqrt]
        calc
          (n - 1) * (n - 1) ≤ n * n :=
            Nat.mul_le_mul (Nat.sub_le n 1) (Nat.sub_le n 1)
          _ ≤ 26 * n := by nlinarith
      omega
    simp only [GenLimit.KleinbergWei.OrderedLanguage.prefixRatio, hn0, if_false]
    apply div_le_div_of_nonneg_right
    · exact_mod_cast ((orderedTarget gen).prefixCount_le core n |>.trans hsqrt)
    · positivity

theorem upperDensity_core_zero (gen : FeedbackGenerator) :
    (orderedTarget gen).upperDensity core = 0 :=
  (tendsto_prefixRatio_core gen).limsup_eq

theorem scored_subset_core (gen : FeedbackGenerator) :
    scored (target gen) (presentation gen) (output gen) ⊆ core := by
  intro z hz
  rcases hz with ⟨hzTarget, t, hyt, hfresh⟩
  rcases hzTarget with hzCore | ⟨s, hsOdd, hs⟩
  · exact hzCore
  · exfalso
    have hts : t < s := by
      by_contra h
      apply hfresh
      exact ⟨s, by omega, hs⟩
    exact later_odd_ne_output gen hts hsOdd (hs.trans hyt.symm)

theorem scored_density_zero (gen : FeedbackGenerator) :
    (orderedTarget gen).upperDensity
      (scored (target gen) (presentation gen) (output gen)) = 0 := by
  apply le_antisymm
  · calc
      (orderedTarget gen).upperDensity
          (scored (target gen) (presentation gen) (output gen)) ≤
          (orderedTarget gen).upperDensity core :=
        (orderedTarget gen).upperDensity_mono (scored_subset_core gen)
      _ = 0 := upperDensity_core_zero gen
  · exact (orderedTarget gen).upperDensity_nonneg _

def presenter (gen : FeedbackGenerator) : CausalPresenter where
  next t x q _a y := choosePresentation t x q y

theorem presentedBy (gen : FeedbackGenerator) :
    PresentedBy (presenter gen) (transcript gen) := by
  intro t
  exact presentation_eq_choose gen t

def liftOrdinary (A : Set ordinary) : Language :=
  {z | ∃ hz : z ∈ ordinary, (⟨z, hz⟩ : ordinary) ∈ A}

theorem liftOrdinary_subset (A : Set ordinary) : liftOrdinary A ⊆ ordinary := by
  rintro z ⟨hz, _⟩
  exact hz

theorem liftOrdinary_mem (A : Set ordinary) (z : ordinary) :
    z.1 ∈ liftOrdinary A ↔ z ∈ A := by
  constructor
  · rintro ⟨hz, h⟩
    simpa using h
  · intro h
    exact ⟨z.2, h⟩

theorem targetClass_uncountable : ¬targetClass.Countable := by
  letI : Infinite ordinary := ordinary_infinite.to_subtype
  intro hcountable
  let f : Set ordinary → targetClass := fun A =>
    ⟨core ∪ liftOrdinary A,
      ⟨liftOrdinary A, liftOrdinary_subset A, rfl⟩⟩
  have hf : Function.Injective f := by
    intro A B hAB
    ext z
    have hsets := congrArg Subtype.val hAB
    have hz := Set.ext_iff.mp hsets z.1
    change z.1 ∈ core ∪ liftOrdinary A ↔
      z.1 ∈ core ∪ liftOrdinary B at hz
    have hnot : z.1 ∉ core := z.2
    rw [Set.mem_union, Set.mem_union, liftOrdinary_mem, liftOrdinary_mem] at hz
    simpa [hnot] using hz
  letI : Countable targetClass := hcountable.to_subtype
  have hpower : Countable (Set ordinary) := hf.countable
  exact GenLimit.UnionClosedness.powerSet_not_countable ordinary hpower

theorem uniformly_generatable : UniformlyGeneratableWithoutSamples := by
  refine ⟨(fun t : ℕ => 2 ^ t), Nat.pow_right_injective (by omega), 0, ?_⟩
  intro K hK t _ht
  obtain ⟨A, _hA, rfl⟩ := hK
  exact Or.inl ⟨t, rfl⟩

theorem negativeClaim : NegativeClaim := by
  intro gen _hgen
  refine ⟨target gen, target_mem_class gen, presenter gen, transcript gen,
    orderedTarget gen, ?_⟩
  refine ⟨rfl, orderedTarget_inherits gen, presentedBy gen,
    followsProtocol gen, presentation_clean gen, presentation_injective gen,
    presentation_complete gen, ?_⟩
  exact scored_density_zero gen

end

end S2BProof

theorem stage3_result : Stage3S2B.MainClaim := by
  exact ⟨S2BProof.targetClass_uncountable,
    S2BProof.uniformly_generatable, S2BProof.negativeClaim⟩
