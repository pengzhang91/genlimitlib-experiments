import Stage3Model
import GenLimit.Paper10_UnionClosednessOfLanguageGeneration.Cardinality
import GenLimit.Paper39_DenseGeneration.Abstract.Density
import Mathlib.Data.Nat.Nth
import Mathlib.Tactic

open Set Filter
open GenLimit.KleinbergWei

namespace Stage3Proof

open Stage3S2B

private def oddCode (n : ℕ) : ℕ := 2 * n + 3

private theorem oddCode_injective : Function.Injective oddCode := by
  intro a b h
  simp [oddCode] at h
  omega

private theorem oddCode_ordinary (n : ℕ) : oddCode n ∈ ordinary := by
  intro h
  rcases h with ⟨k, hk⟩
  have hodd : Odd (oddCode n) := by
    refine ⟨n + 1, ?_⟩
    simp [oddCode]
    omega
  have hpow : Odd (2 ^ k) := by simpa [hk] using hodd
  have hk0 : k = 0 := by
    by_contra hk0
    have : Even (2 ^ k) := Nat.even_pow.mpr ⟨even_two, hk0⟩
    exact (Nat.not_even_iff_odd.mpr hpow) this
  simp [hk0, oddCode] at hk

structure Hist (t : ℕ) where
  x : Fin t → ℕ
  q : Fin t → Option ℕ
  a : Fin t → Option Bool
  y : Fin t → ℕ

private def bad {t : ℕ} (h : Hist t) : Finset ℕ :=
  (Finset.univ.image h.x ∪ Finset.univ.image (fun i => (h.q i).getD 0)) ∪
    Finset.univ.image h.y

private theorem bad_card_le {t : ℕ} (h : Hist t) : (bad h).card ≤ 3 * t := by
  unfold bad
  calc
    ((Finset.univ.image h.x ∪ Finset.univ.image (fun i => (h.q i).getD 0)) ∪
        Finset.univ.image h.y).card
        ≤ (Finset.univ.image h.x ∪
            Finset.univ.image (fun i => (h.q i).getD 0)).card +
          (Finset.univ.image h.y).card := Finset.card_union_le _ _
    _ ≤ ((Finset.univ.image h.x).card +
          (Finset.univ.image (fun i => (h.q i).getD 0)).card) +
          (Finset.univ.image h.y).card := by
            gcongr
            exact Finset.card_union_le _ _
    _ ≤ t + t + t := by
      gcongr <;> simpa using (Finset.card_image_le :
        (Finset.univ.image (_ : Fin t → ℕ)).card ≤ Finset.univ.card)
    _ = 3 * t := by omega

private theorem exists_fresh {t : ℕ} (h : Hist t) :
    ∃ z, z ∈ (Finset.range (3 * t + 1)).image oddCode ∧ z ∉ bad h := by
  let candidates := (Finset.range (3 * t + 1)).image oddCode
  have hc : candidates.card = 3 * t + 1 := by
    simpa [candidates] using
      (Finset.card_image_of_injective (Finset.range (3 * t + 1)) oddCode_injective)
  obtain ⟨z, hzC, hzbad⟩ :=
    Finset.exists_mem_not_mem_of_card_lt_card
      (show (bad h).card < candidates.card by
        rw [hc]
        exact lt_of_le_of_lt (bad_card_le h) (by omega))
  exact ⟨z, hzC, hzbad⟩

private noncomputable def fresh {t : ℕ} (h : Hist t) : ℕ :=
  Classical.choose (exists_fresh h)

private theorem fresh_spec {t : ℕ} (h : Hist t) :
    fresh h ∈ (Finset.range (3 * t + 1)).image oddCode ∧ fresh h ∉ bad h :=
  Classical.choose_spec (exists_fresh h)

private theorem fresh_bound {t : ℕ} (h : Hist t) : fresh h ≤ 6 * t + 3 := by
  rcases Finset.mem_image.mp (fresh_spec h).1 with ⟨n, hn, heq⟩
  simp only [Finset.mem_range] at hn
  rw [← heq]
  simp [oddCode]
  omega

private theorem fresh_ordinary {t : ℕ} (h : Hist t) : fresh h ∈ ordinary := by
  rcases Finset.mem_image.mp (fresh_spec h).1 with ⟨n, -, heq⟩
  rw [← heq]
  exact oddCode_ordinary n

private theorem fresh_ne_x {t : ℕ} (h : Hist t) (i : Fin t) : fresh h ≠ h.x i := by
  intro heq
  exact (fresh_spec h).2 (by simp [bad, heq])

private theorem fresh_ne_q {t : ℕ} (h : Hist t) (i : Fin t) (z : ℕ)
    (hq : h.q i = some z) : fresh h ≠ z := by
  intro heq
  apply (fresh_spec h).2
  simp only [bad, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
  exact Or.inl (Or.inr ⟨i, by simp [hq, heq]⟩)

private theorem fresh_ne_y {t : ℕ} (h : Hist t) (i : Fin t) : fresh h ≠ h.y i := by
  intro heq
  exact (fresh_spec h).2 (by simp [bad, heq])

structure Step (t : ℕ) where
  nx : ℕ
  nq : Option ℕ
  na : Option Bool
  ny : ℕ

private noncomputable def nextX {t : ℕ} (h : Hist t) : ℕ :=
  if Even t then 2 ^ (t / 2) else fresh h

private noncomputable def makeStep (gen : FeedbackGenerator) {t : ℕ} (h : Hist t) : Step t := by
  classical
  let nx := nextX h
  let xx : Fin (t + 1) → ℕ := Fin.snoc h.x nx
  let nq := gen.query t xx h.a
  let na := match nq with
    | none => none
    | some z => some (decide (z ∈ core ∨ ∃ i, xx i = z))
  let aa : Fin (t + 1) → Option Bool := Fin.snoc h.a na
  exact ⟨nx, nq, na, gen.output t xx aa⟩

private noncomputable def extend (gen : FeedbackGenerator) {t : ℕ} (h : Hist t) : Hist (t + 1) :=
  let s := makeStep gen h
  ⟨Fin.snoc h.x s.nx, Fin.snoc h.q s.nq, Fin.snoc h.a s.na, Fin.snoc h.y s.ny⟩

private noncomputable def histories (gen : FeedbackGenerator) : (t : ℕ) → Hist t
  | 0 => ⟨Fin.elim0, Fin.elim0, Fin.elim0, Fin.elim0⟩
  | t + 1 => extend gen (histories gen t)

private noncomputable def adversarialTranscript (gen : FeedbackGenerator) : Transcript where
  presentation t := (makeStep gen (histories gen t)).nx
  query t := (makeStep gen (histories gen t)).nq
  answer t := (makeStep gen (histories gen t)).na
  output t := (makeStep gen (histories gen t)).ny

private theorem histories_x (gen : FeedbackGenerator) (t : ℕ) :
    (histories gen t).x = fun i : Fin t => (adversarialTranscript gen).presentation i := by
  induction t with
  | zero => funext i; exact Fin.elim0 i
  | succ t ih =>
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [histories, extend, adversarialTranscript]
      · simp [histories, extend, adversarialTranscript, ih]

private theorem histories_q (gen : FeedbackGenerator) (t : ℕ) :
    (histories gen t).q = fun i : Fin t => (adversarialTranscript gen).query i := by
  induction t with
  | zero => funext i; exact Fin.elim0 i
  | succ t ih =>
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [histories, extend, adversarialTranscript]
      · simp [histories, extend, adversarialTranscript, ih]

private theorem histories_a (gen : FeedbackGenerator) (t : ℕ) :
    (histories gen t).a = fun i : Fin t => (adversarialTranscript gen).answer i := by
  induction t with
  | zero => funext i; exact Fin.elim0 i
  | succ t ih =>
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [histories, extend, adversarialTranscript]
      · simp [histories, extend, adversarialTranscript, ih]

private theorem histories_y (gen : FeedbackGenerator) (t : ℕ) :
    (histories gen t).y = fun i : Fin t => (adversarialTranscript gen).output i := by
  induction t with
  | zero => funext i; exact Fin.elim0 i
  | succ t ih =>
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [histories, extend, adversarialTranscript]
      · simp [histories, extend, adversarialTranscript, ih]

private theorem presentation_even (gen : FeedbackGenerator) (n : ℕ) :
    (adversarialTranscript gen).presentation (2 * n) = 2 ^ n := by
  simp [adversarialTranscript, makeStep, nextX]

private theorem presentation_odd (gen : FeedbackGenerator) (n : ℕ) :
    (adversarialTranscript gen).presentation (2 * n + 1) =
      fresh (histories gen (2 * n + 1)) := by
  simp [adversarialTranscript, makeStep, nextX]

private theorem presentation_odd_ordinary (gen : FeedbackGenerator) (n : ℕ) :
    (adversarialTranscript gen).presentation (2 * n + 1) ∈ ordinary := by
  rw [presentation_odd]
  exact fresh_ordinary _

private theorem presentation_odd_bound (gen : FeedbackGenerator) (n : ℕ) :
    (adversarialTranscript gen).presentation (2 * n + 1) ≤ 12 * n + 9 := by
  rw [presentation_odd]
  have := fresh_bound (histories gen (2 * n + 1))
  omega

private theorem presentation_injective (gen : FeedbackGenerator) :
    Function.Injective (adversarialTranscript gen).presentation := by
  intro s t hst
  apply le_antisymm
  · by_contra hnot
    have hts : t < s := Nat.lt_of_not_ge hnot
    by_cases hs : Even s
    · rcases hs with ⟨n, rfl⟩
      by_cases ht : Even t
      · rcases ht with ⟨m, rfl⟩
        rw [show m + m = 2 * m by omega, show n + n = 2 * n by omega,
          presentation_even, presentation_even] at hst
        have : m < n := by omega
        exact (pow_lt_pow_right₀ (by omega : 1 < (2 : ℕ)) this).ne hst.symm
      · have htodd : Odd t := Nat.not_even_iff_odd.mp ht
        rcases htodd with ⟨m, rfl⟩
        have hord := presentation_odd_ordinary gen m
        apply hord
        refine ⟨n, ?_⟩
        rw [← hst]
        simpa [two_mul] using (presentation_even gen n).symm
    · have hsodd : Odd s := Nat.not_even_iff_odd.mp hs
      rcases hsodd with ⟨n, rfl⟩
      rw [presentation_odd] at hst
      have hne := fresh_ne_x (histories gen (2 * n + 1))
        ⟨t, by omega⟩
      apply hne
      rw [histories_x]
      exact hst
  · by_contra hnot
    have hstlt : s < t := Nat.lt_of_not_ge hnot
    by_cases ht : Even t
    · rcases ht with ⟨n, rfl⟩
      by_cases hs : Even s
      · rcases hs with ⟨m, rfl⟩
        rw [show m + m = 2 * m by omega, show n + n = 2 * n by omega,
          presentation_even, presentation_even] at hst
        have : m < n := by omega
        exact (pow_lt_pow_right₀ (by omega : 1 < (2 : ℕ)) this).ne hst
      · have hsodd : Odd s := Nat.not_even_iff_odd.mp hs
        rcases hsodd with ⟨m, rfl⟩
        have hord := presentation_odd_ordinary gen m
        apply hord
        refine ⟨n, ?_⟩
        rw [hst]
        simpa [two_mul] using (presentation_even gen n).symm
    · have htodd : Odd t := Nat.not_even_iff_odd.mp ht
      rcases htodd with ⟨n, rfl⟩
      rw [presentation_odd] at hst
      have hne := fresh_ne_x (histories gen (2 * n + 1))
        ⟨s, by omega⟩
      apply hne
      rw [histories_x]
      exact hst.symm


private noncomputable def finalTarget (gen : FeedbackGenerator) : Language :=
  core ∪ Set.range (adversarialTranscript gen).presentation

private theorem finalTarget_mem_class (gen : FeedbackGenerator) :
    finalTarget gen ∈ targetClass := by
  refine ⟨Set.range (adversarialTranscript gen).presentation \ core, ?_, ?_⟩
  · intro z hz
    exact hz.2
  · ext z
    simp only [finalTarget, Set.mem_union, Set.mem_diff, Set.mem_range,
      Set.mem_compl_iff]
    tauto

private theorem finalTarget_clean (gen : FeedbackGenerator) :
    Clean (adversarialTranscript gen).presentation (finalTarget gen) := by
  intro t
  exact Or.inr ⟨t, rfl⟩

private theorem finalTarget_complete (gen : FeedbackGenerator) :
    Complete (adversarialTranscript gen).presentation (finalTarget gen) := by
  intro z hz
  rcases hz with hz | ⟨t, rfl⟩
  · rcases hz with ⟨n, rfl⟩
    exact ⟨2 * n, presentation_even gen n⟩
  · exact ⟨t, rfl⟩

private theorem future_ne_query (gen : FeedbackGenerator) {t s z : ℕ}
    (hts : t < s) (hq : (adversarialTranscript gen).query t = some z)
    (hz : z ∉ core) : (adversarialTranscript gen).presentation s ≠ z := by
  intro hs
  by_cases he : Even s
  · rcases he with ⟨n, rfl⟩
    apply hz
    have hs' : (adversarialTranscript gen).presentation (2 * n) = z := by
      simpa [two_mul] using hs
    exact ⟨n, (presentation_even gen n).symm.trans hs'⟩
  · rcases Nat.not_even_iff_odd.mp he with ⟨n, rfl⟩
    rw [presentation_odd] at hs
    have hne := fresh_ne_q (histories gen (2 * n + 1))
      ⟨t, by omega⟩ z
    apply hne
    · rw [histories_q]
      exact hq
    · exact hs

private theorem future_ne_output (gen : FeedbackGenerator) {t s z : ℕ}
    (hts : t < s) (hy : (adversarialTranscript gen).output t = z)
    (hz : z ∉ core) : (adversarialTranscript gen).presentation s ≠ z := by
  intro hs
  by_cases he : Even s
  · rcases he with ⟨n, rfl⟩
    apply hz
    have hs' : (adversarialTranscript gen).presentation (2 * n) = z := by
      simpa [two_mul] using hs
    exact ⟨n, (presentation_even gen n).symm.trans hs'⟩
  · rcases Nat.not_even_iff_odd.mp he with ⟨n, rfl⟩
    rw [presentation_odd] at hs
    have hne := fresh_ne_y (histories gen (2 * n + 1)) ⟨t, by omega⟩
    apply hne
    rw [histories_y]
    exact hs.trans hy.symm

private theorem query_condition_iff (gen : FeedbackGenerator) (t z : ℕ)
    (hq : (adversarialTranscript gen).query t = some z) :
    (z ∈ core ∨ ∃ i : Fin (t + 1),
      (adversarialTranscript gen).presentation i = z) ↔ z ∈ finalTarget gen := by
  constructor
  · rintro (hz | ⟨i, hi⟩)
    · exact Or.inl hz
    · exact Or.inr ⟨i, hi⟩
  · rintro (hz | ⟨s, hs⟩)
    · exact Or.inl hz
    · by_cases hst : s ≤ t
      · exact Or.inr ⟨⟨s, by omega⟩, hs⟩
      · have hts : t < s := Nat.lt_of_not_ge hst
        by_cases hzcore : z ∈ core
        · exact Or.inl hzcore
        · exact False.elim ((future_ne_query gen hts hq hzcore) hs)


private theorem current_x (gen : FeedbackGenerator) (t : ℕ) :
    Fin.snoc (histories gen t).x (nextX (histories gen t)) =
      fun i : Fin (t + 1) => (adversarialTranscript gen).presentation i := by
  simpa [histories, extend] using histories_x gen (t + 1)

private theorem current_a (gen : FeedbackGenerator) (t : ℕ) :
    Fin.snoc (histories gen t).a (makeStep gen (histories gen t)).na =
      fun i : Fin (t + 1) => (adversarialTranscript gen).answer i := by
  simpa [histories, extend] using histories_a gen (t + 1)

private theorem query_eq (gen : FeedbackGenerator) (t : ℕ) :
    (adversarialTranscript gen).query t = gen.query t
      (fun i => (adversarialTranscript gen).presentation i)
      (fun i => (adversarialTranscript gen).answer i) := by
  change gen.query t (Fin.snoc (histories gen t).x (nextX (histories gen t)))
    (histories gen t).a = _
  rw [current_x, histories_a]

private theorem output_eq (gen : FeedbackGenerator) (t : ℕ) :
    (adversarialTranscript gen).output t = gen.output t
      (fun i => (adversarialTranscript gen).presentation i)
      (fun i => (adversarialTranscript gen).answer i) := by
  change gen.output t
    (Fin.snoc (histories gen t).x (nextX (histories gen t)))
    (Fin.snoc (histories gen t).a (makeStep gen (histories gen t)).na) = _
  rw [current_x, current_a]

private theorem answer_eq (gen : FeedbackGenerator) (t : ℕ) :
    (adversarialTranscript gen).answer t =
      match (adversarialTranscript gen).query t with
      | none => none
      | some z => some (membershipAnswer (finalTarget gen) z) := by
  change (makeStep gen (histories gen t)).na = _
  rw [query_eq]
  simp only [makeStep]
  rw [current_x, histories_a]
  generalize hq : gen.query t
      (fun i : Fin (t + 1) => (adversarialTranscript gen).presentation i)
      (fun i : Fin t => (adversarialTranscript gen).answer i) = oq
  cases oq with
  | none => rfl
  | some z =>
      have hq' : (adversarialTranscript gen).query t = some z := by
        rw [query_eq, hq]
      have hiff := query_condition_iff gen t z hq'
      simp only [membershipAnswer]
      congr 2
      exact propext hiff

private theorem follows_finalTarget (gen : FeedbackGenerator) :
    FollowsProtocol gen (finalTarget gen) (adversarialTranscript gen) := by
  intro t
  exact ⟨query_eq gen t, answer_eq gen t, output_eq gen t⟩

private theorem eventual_output_core (gen : FeedbackGenerator)
    (hgen : UniversallyEventuallyValidFresh gen) :
    ∃ T, ∀ t, T ≤ t → (adversarialTranscript gen).output t ∈ core := by
  obtain ⟨T, hT⟩ := hgen (finalTarget gen) (finalTarget_mem_class gen)
    (adversarialTranscript gen) (follows_finalTarget gen)
    (finalTarget_clean gen) (presentation_injective gen)
    (finalTarget_complete gen)
  refine ⟨T, fun t ht => ?_⟩
  rcases (hT t ht).1 with hycore | ⟨s, hs⟩
  · exact hycore
  · by_contra hycore
    have hfuture : t < s := by
      by_contra hnot
      have hst : s ≤ t := Nat.le_of_not_gt hnot
      exact (hT t ht).2 ⟨s, hst, hs⟩
    exact (future_ne_output gen hfuture rfl hycore) hs


private theorem finalTarget_infinite (gen : FeedbackGenerator) :
    (finalTarget gen).Infinite := by
  apply (Set.infinite_range_of_injective (Nat.pow_right_injective (by omega : 2 ≤ 2))).mono
  intro z hz
  exact Or.inl hz

private noncomputable def orderedTarget (gen : FeedbackGenerator) : Stage3S2B.OrderedLanguage where
  carrier := finalTarget gen
  enumeration := Nat.nth (fun z => z ∈ finalTarget gen)
  enumeration_injective := (Nat.nth_strictMono (finalTarget_infinite gen)).injective
  range_enumeration := Nat.range_nth_of_infinite (finalTarget_infinite gen)

private theorem orderedTarget_strict (gen : FeedbackGenerator) :
    InheritsAmbientOrder (orderedTarget gen) :=
  Nat.nth_strictMono (finalTarget_infinite gen)

private theorem enumeration_bound (gen : FeedbackGenerator) (n : ℕ) :
    (orderedTarget gen).enumeration n < 12 * n + 10 := by
  classical
  let samples : Finset ℕ :=
    Finset.univ.image (fun i : Fin (n + 1) =>
      (adversarialTranscript gen).presentation (2 * (i : ℕ) + 1))
  have hsCard : samples.card = n + 1 := by
    rw [Finset.card_image_of_injective]
    · simp
    · intro i j hij
      apply Fin.ext
      have hp := presentation_injective gen hij
      omega
  have hsSub : samples ⊆
      (Finset.range (12 * n + 10)).filter (fun z => z ∈ finalTarget gen) := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨i, -, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · have hb := presentation_odd_bound gen (i : ℕ)
      have hi : (i : ℕ) ≤ n := Nat.le_of_lt_succ i.isLt
      omega
    · exact Or.inr ⟨2 * (i : ℕ) + 1, rfl⟩
  apply Nat.nth_lt_of_lt_count
  rw [Nat.count_eq_card_filter_range]
  have hc := Finset.card_le_card hsSub
  rw [hsCard] at hc
  omega

private theorem core_prefixCount_bound (gen : FeedbackGenerator) (n : ℕ) :
    (orderedTarget gen).prefixCount core n ≤ Nat.log2 (12 * n + 10) + 1 := by
  classical
  let indices := (Finset.range n).filter
    (fun i => (orderedTarget gen).enumeration i ∈ core)
  let powers := (Finset.range (Nat.log2 (12 * n + 10) + 1)).image
    (fun k => 2 ^ k)
  have hsub : indices.image (orderedTarget gen).enumeration ⊆ powers := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨i, hi, rfl⟩
    have hi' := (Finset.mem_filter.mp hi)
    rcases hi'.2 with ⟨k, hk⟩
    apply Finset.mem_image.mpr
    refine ⟨k, ?_, hk⟩
    simp only [Finset.mem_range]
    apply Nat.lt_succ_of_le
    rw [Nat.le_log2 (by omega : 12 * n + 10 ≠ 0)]
    have hin : i < n := Finset.mem_range.mp hi'.1
    calc
      2 ^ k = (orderedTarget gen).enumeration i := hk
      _ ≤ (orderedTarget gen).enumeration n := (orderedTarget_strict gen hin).le
      _ ≤ 12 * n + 10 := Nat.le_of_lt (enumeration_bound gen n)
  have hcardImage :
      (indices.image (orderedTarget gen).enumeration).card = indices.card := by
    exact Finset.card_image_of_injective _ (orderedTarget gen).enumeration_injective
  have hpCard : powers.card ≤ Nat.log2 (12 * n + 10) + 1 := by
    exact (Finset.card_image_le).trans_eq (Finset.card_range _)
  unfold GenLimit.KleinbergWei.OrderedLanguage.prefixCount
  change indices.card ≤ _
  rw [← hcardImage]
  exact (Finset.card_le_card hsub).trans hpCard

private theorem log_bound (n : ℕ) (hn : 0 < n) :
    Nat.log2 (12 * n + 10) + 1 ≤ Nat.log2 n + 6 := by
  have hn0 : n ≠ 0 := by omega
  have hnpow : n < 2 ^ (Nat.log2 n + 1) := by
    rw [← Nat.log2_lt hn0]
    omega
  have hbig : 12 * n + 10 < 2 ^ (Nat.log2 n + 6) := by
    calc
      12 * n + 10 ≤ 32 * n := by omega
      _ < 32 * 2 ^ (Nat.log2 n + 1) := by omega
      _ = 2 ^ (Nat.log2 n + 6) := by ring
  have hlog : Nat.log2 (12 * n + 10) < Nat.log2 n + 6 := by
    rw [Nat.log2_lt (by omega : 12 * n + 10 ≠ 0)]
    exact hbig
  omega

private theorem core_prefixRatio_tendsto_zero (gen : FeedbackGenerator) :
    Tendsto ((orderedTarget gen).prefixRatio core) atTop (nhds (0 : ℝ)) := by
  have hupper : ∀ n,
      (orderedTarget gen).prefixRatio core n ≤
        ((Nat.log2 n + 6 : ℕ) : ℝ) / n := by
    intro n
    by_cases hn : n = 0
    · simp [hn]
    · simp only [OrderedLanguage.prefixRatio, hn, if_false]
      apply div_le_div_of_nonneg_right
      · exact_mod_cast (core_prefixCount_bound gen n).trans (log_bound n (Nat.pos_of_ne_zero hn))
      · positivity
  apply squeeze_zero
    (fun n => (orderedTarget gen).prefixRatio_nonneg core n) hupper
  have hc : Tendsto (fun n : ℕ => (6 : ℝ) / (n : ℝ)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  simpa only [Nat.cast_add, Nat.cast_ofNat, add_div, zero_add] using
    GenLimit.tendsto_natLog2_div.add hc

private theorem core_upperDensity_zero (gen : FeedbackGenerator) :
    (orderedTarget gen).upperDensity core = 0 := by
  exact (core_prefixRatio_tendsto_zero gen).limsup_eq

private theorem scored_subset_core_union_finite (gen : FeedbackGenerator)
    (hgen : UniversallyEventuallyValidFresh gen) :
    ∃ T, scored (finalTarget gen) (adversarialTranscript gen).presentation
        (adversarialTranscript gen).output ⊆
      core ∪ Set.range (fun i : Fin T => (adversarialTranscript gen).output i) := by
  obtain ⟨T, hT⟩ := eventual_output_core gen hgen
  refine ⟨T, ?_⟩
  intro z hz
  rcases hz with ⟨-, t, hyt, -⟩
  by_cases ht : T ≤ t
  · exact Or.inl (hyt ▸ hT t ht)
  · exact Or.inr ⟨⟨t, by omega⟩, hyt⟩

private theorem scored_upperDensity_zero (gen : FeedbackGenerator)
    (hgen : UniversallyEventuallyValidFresh gen) :
    (orderedTarget gen).upperDensity
      (scored (finalTarget gen) (adversarialTranscript gen).presentation
        (adversarialTranscript gen).output) = 0 := by
  obtain ⟨T, hsub⟩ := scored_subset_core_union_finite gen hgen
  let F : Language := Set.range (fun i : Fin T => (adversarialTranscript gen).output i)
  have hF : F.Finite := Set.toFinite _
  apply le_antisymm
  · calc
      (orderedTarget gen).upperDensity
          (scored (finalTarget gen) (adversarialTranscript gen).presentation
            (adversarialTranscript gen).output)
          ≤ (orderedTarget gen).upperDensity (core ∪ F) :=
            (orderedTarget gen).upperDensity_mono hsub
      _ ≤ (orderedTarget gen).upperDensity core +
          (orderedTarget gen).upperDensity F :=
            (orderedTarget gen).upperDensity_union_le _ _
      _ = 0 := by rw [core_upperDensity_zero,
        (orderedTarget gen).upperDensity_eq_zero_of_finite hF, zero_add]
  · exact (orderedTarget gen).upperDensity_nonneg _

private noncomputable def finalPresenter (gen : FeedbackGenerator) : CausalPresenter where
  next t _ _ _ _ := (adversarialTranscript gen).presentation t

private theorem presented_final (gen : FeedbackGenerator) :
    PresentedBy (finalPresenter gen) (adversarialTranscript gen) := by
  intro t
  rfl

private theorem negative_claim : NegativeClaim := by
  intro gen hgen
  refine ⟨finalTarget gen, finalTarget_mem_class gen, finalPresenter gen,
    adversarialTranscript gen, orderedTarget gen, ?_⟩
  exact ⟨rfl, orderedTarget_strict gen, presented_final gen,
    follows_finalTarget gen, finalTarget_clean gen, presentation_injective gen,
    finalTarget_complete gen, scored_upperDensity_zero gen hgen⟩


private def encodeTarget (A : Set {z : ℕ // z ∈ ordinary}) : Language :=
  core ∪ Subtype.val '' A

private theorem encodeTarget_mem (A : Set {z : ℕ // z ∈ ordinary}) :
    encodeTarget A ∈ targetClass := by
  refine ⟨Subtype.val '' A, ?_, rfl⟩
  rintro z ⟨a, -, rfl⟩
  exact a.property

private theorem encodeTarget_injective : Function.Injective encodeTarget := by
  intro A B hAB
  ext a
  have ha : (a : ℕ) ∉ core := a.property
  have hmemA : (a : ℕ) ∈ encodeTarget A ↔ a ∈ A := by
    simp [encodeTarget, ha]
  have hmemB : (a : ℕ) ∈ encodeTarget B ↔ a ∈ B := by
    simp [encodeTarget, ha]
  rw [← hmemA, hAB, hmemB]

private theorem target_not_countable : ¬ targetClass.Countable := by
  intro hcount
  letI : Countable {K : Language // K ∈ targetClass} :=
    Set.countable_coe_iff.mpr hcount
  let embedding : Set {z : ℕ // z ∈ ordinary} →
      {K : Language // K ∈ targetClass} :=
    fun A => ⟨encodeTarget A, encodeTarget_mem A⟩
  have hemb : Function.Injective embedding := by
    intro A B h
    apply encodeTarget_injective
    exact congrArg Subtype.val h
  have hsets : Countable (Set {z : ℕ // z ∈ ordinary}) := hemb.countable
  have hord : ordinary.Infinite := by
    apply (Set.infinite_range_of_injective oddCode_injective).mono
    rintro z ⟨n, rfl⟩
    exact oddCode_ordinary n
  letI : Infinite {z : ℕ // z ∈ ordinary} := Set.infinite_coe_iff.mpr hord
  exact GenLimit.UnionClosedness.powerSet_not_countable
    {z : ℕ // z ∈ ordinary} hsets

private theorem uniform_claim : UniformlyGeneratableWithoutSamples := by
  refine ⟨fun t => 2 ^ t, Nat.pow_right_injective (by omega), 0, ?_⟩
  intro K hK t _
  rcases hK with ⟨A, hA, rfl⟩
  exact Or.inl ⟨t, rfl⟩

end Stage3Proof

open Stage3Proof

theorem stage3_result : Stage3S2B.MainClaim := by
  exact ⟨target_not_countable, uniform_claim, negative_claim⟩
