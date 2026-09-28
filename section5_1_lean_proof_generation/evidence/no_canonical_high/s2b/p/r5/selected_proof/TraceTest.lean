import S2BFormalization
import Mathlib.Data.Nat.Nth
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

open Set Filter
open scoped Topology

set_option maxHeartbeats 1000000

namespace Stage3Proof
open Stage3S2B

structure Round where
  presented : ℕ
  query : Option ℕ
  answer : Option Bool
  output : ℕ


def snoc {α : Type*} {t : ℕ} (past : Fin t → α) (last : α) : Fin (t + 1) → α :=
  fun i => if h : i.val < t then past ⟨i.val, h⟩ else last

lemma snoc_apply {α : Type*} (f : ℕ → α) (t : ℕ) (i : Fin (t + 1)) :
    snoc (fun j : Fin t => f j.val) (f t) i = f i.val := by
  simp only [snoc]
  split <;> rename_i h
  · rfl
  · congr 1
    omega


lemma exists_freshIndex (used : Finset ℕ) : ∃ n, oddCode n ∉ used := by
  classical
  rcases (Set.infinite_range_of_injective oddCode_injective).exists_notMem_finset used with
    ⟨z, ⟨n, rfl⟩, hn⟩
  exact ⟨n, hn⟩

noncomputable def freshIndex (used : Finset ℕ) : ℕ :=
  Nat.find (exists_freshIndex used)

lemma freshIndex_not_mem (used : Finset ℕ) : oddCode (freshIndex used) ∉ used :=
  Nat.find_spec (exists_freshIndex used)

lemma freshIndex_le_card (used : Finset ℕ) : freshIndex used ≤ used.card := by
  classical
  let candidates := (Finset.range (used.card + 1)).image oddCode
  have hcard : used.card < candidates.card := by
    simp [candidates, Finset.card_image_of_injective _ oddCode_injective]
  rcases Finset.exists_mem_notMem_of_card_lt_card hcard with ⟨z, hz, hnot⟩
  rcases Finset.mem_image.mp hz with ⟨n, hn, rfl⟩
  exact (Nat.find_min' _ hnot).trans (Nat.le_of_lt_succ (Finset.mem_range.mp hn))

noncomputable def run (gen : FeedbackGenerator) (t : ℕ) : Round := by
  classical
  let priorX : Fin t → ℕ := fun i => (run gen i.val).presented
  let priorQ : Fin t → Option ℕ := fun i => (run gen i.val).query
  let priorA : Fin t → Option Bool := fun i => (run gen i.val).answer
  let priorY : Fin t → ℕ := fun i => (run gen i.val).output
  let used : Finset ℕ :=
    (Finset.univ.image priorX) ∪
    (Finset.univ.image fun i => (priorQ i).getD 0) ∪
    (Finset.univ.image priorY)
  let x := if t % 2 = 0 then 2 ^ (t / 2) else oddCode (freshIndex used)
  let q := gen.query t (snoc priorX x) priorA
  let a := match q with
    | none => none
    | some z => some (decide (z ∈ core ∨ z = x ∨ z ∈ Finset.univ.image priorX))
  let y := gen.output t (snoc priorX x) (snoc priorA a)
  exact ⟨x, q, a, y⟩
termination_by t
decreasing_by all_goals exact Fin.isLt _

noncomputable def usedBefore (gen : FeedbackGenerator) (t : ℕ) : Finset ℕ :=
  (Finset.univ.image (fun i : Fin t => (run gen i.val).presented)) ∪
  (Finset.univ.image (fun i : Fin t => ((run gen i.val).query).getD 0)) ∪
  (Finset.univ.image (fun i : Fin t => (run gen i.val).output))

lemma presented_odd_eq (gen : FeedbackGenerator) {t : ℕ} (ht : t % 2 ≠ 0) :
    (run gen t).presented = oddCode (freshIndex (usedBefore gen t)) := by
  rw [run.eq_def]
  dsimp only [Round.presented, usedBefore]
  simp only [if_neg ht]

noncomputable def adversarialTrace (gen : FeedbackGenerator) : Transcript where
  presentation t := (run gen t).presented
  query t := (run gen t).query
  answer t := (run gen t).answer
  output t := (run gen t).output

noncomputable def adversarialTarget (gen : FeedbackGenerator) : Language :=
  Set.range (adversarialTrace gen).presentation

lemma run_query_eq (gen : FeedbackGenerator) (t : ℕ) :
    (run gen t).query = gen.query t
      (fun i => (run gen i).presented) (fun i => (run gen i).answer) := by
  rw [run.eq_def]
  dsimp only [Round.query]
  congr 2
  funext i
  convert snoc_apply (fun n => (run gen n).presented) t i using 1
  symm
  rw [run.eq_def]

lemma run_output_eq (gen : FeedbackGenerator) (t : ℕ) :
    (run gen t).output = gen.output t
      (fun i => (run gen i).presented) (fun i => (run gen i).answer) := by
  rw [run.eq_def]
  dsimp only [Round.output]
  congr 2
  · funext i
    convert snoc_apply (fun n => (run gen n).presented) t i using 1
    symm
    rw [run.eq_def]
  · funext i
    convert snoc_apply (fun n => (run gen n).answer) t i using 1
    symm
    rw [run.eq_def]

end Stage3Proof

namespace Stage3Proof
open Stage3S2B

lemma presented_even (gen : FeedbackGenerator) {t : ℕ} (ht : t % 2 = 0) :
    (run gen t).presented = 2 ^ (t / 2) := by
  rw [run.eq_def]
  dsimp only [Round.presented]
  simp [ht]

lemma presented_odd (gen : FeedbackGenerator) {t : ℕ} (ht : t % 2 ≠ 0) :
    ∃ n, (run gen t).presented = oddCode n := by
  rw [run.eq_def]
  dsimp only [Round.presented]
  simp only [if_neg ht]
  exact ⟨_, rfl⟩

lemma presented_two_mul (gen : FeedbackGenerator) (k : ℕ) :
    (run gen (2 * k)).presented = 2 ^ k := by
  rw [presented_even gen (by omega)]
  congr 1
  omega

lemma presented_odd_mem_ordinary (gen : FeedbackGenerator) {t : ℕ} (ht : t % 2 ≠ 0) :
    (run gen t).presented ∈ ordinary := by
  rcases presented_odd gen ht with ⟨n, hn⟩
  rw [hn]
  exact oddCode_mem_ordinary n

lemma future_odd_ne_presented (gen : FeedbackGenerator) {s t : ℕ}
    (hst : s < t) (ht : t % 2 ≠ 0) :
    (run gen t).presented ≠ (run gen s).presented := by
  rw [presented_odd_eq gen ht]
  intro heq
  apply (freshIndex_not_mem (usedBefore gen t))
  unfold usedBefore
  exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl
    (Finset.mem_image.mpr
      ⟨(⟨s, hst⟩ : Fin t), Finset.mem_univ _, heq.symm⟩))))

lemma future_odd_ne_output (gen : FeedbackGenerator) {s t : ℕ}
    (hst : s < t) (ht : t % 2 ≠ 0) :
    (run gen t).presented ≠ (run gen s).output := by
  rw [presented_odd_eq gen ht]
  intro heq
  apply (freshIndex_not_mem (usedBefore gen t))
  unfold usedBefore
  exact Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr
    ⟨(⟨s, hst⟩ : Fin t), Finset.mem_univ _, heq.symm⟩))

lemma future_odd_ne_query (gen : FeedbackGenerator) {s t z : ℕ}
    (hst : s < t) (ht : t % 2 ≠ 0) (hq : (run gen s).query = some z) :
    (run gen t).presented ≠ z := by
  rw [presented_odd_eq gen ht]
  intro heq
  apply (freshIndex_not_mem (usedBefore gen t))
  have hget : ((run gen s).query).getD 0 = z := by simp [hq]
  unfold usedBefore
  exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr
    (Finset.mem_image.mpr
      ⟨(⟨s, hst⟩ : Fin t), Finset.mem_univ _, hget.trans heq.symm⟩))))

lemma used_card_le (gen : FeedbackGenerator) (t : ℕ) :
    (usedBefore gen t).card ≤ 3 * t := by
  unfold usedBefore
  calc
    _ ≤ (Finset.univ.image (fun i : Fin t => (run gen i.val).presented)).card +
        (Finset.univ.image (fun i : Fin t => ((run gen i.val).query).getD 0)).card +
        (Finset.univ.image (fun i : Fin t => (run gen i.val).output)).card := by
          exact (Finset.card_union_le _ _).trans
            (Nat.add_le_add_right (Finset.card_union_le _ _) _)
    _ ≤ t + t + t := by
      gcongr
      · simpa using (Finset.card_image_le
          (s := (Finset.univ : Finset (Fin t)))
          (f := fun i : Fin t => (run gen i.val).presented))
      · simpa using (Finset.card_image_le
          (s := (Finset.univ : Finset (Fin t)))
          (f := fun i : Fin t => ((run gen i.val).query).getD 0))
      · simpa using (Finset.card_image_le
          (s := (Finset.univ : Finset (Fin t)))
          (f := fun i : Fin t => (run gen i.val).output))
    _ = 3 * t := by omega

lemma presented_odd_bound (gen : FeedbackGenerator) {t : ℕ} (ht : t % 2 ≠ 0) :
    (run gen t).presented ≤ 6 * t + 3 := by
  rw [presented_odd_eq gen ht]
  unfold oddCode
  have hfresh := freshIndex_le_card (usedBefore gen t)
  have hcard := used_card_le gen t
  omega

end Stage3Proof

namespace Stage3Proof
open Stage3S2B

lemma adversarialTarget_mem (gen : FeedbackGenerator) :
    adversarialTarget gen ∈ targetClass := by
  refine ⟨adversarialTarget gen \ core, ?_, ?_⟩
  · simpa only [ordinary] using
      (Set.diff_subset_compl (adversarialTarget gen) core)
  · ext z
    constructor
    · rintro ⟨t, rfl⟩
      by_cases hz : (run gen t).presented ∈ core
      · exact Or.inl hz
      · exact Or.inr ⟨⟨t, rfl⟩, hz⟩
    · rintro (hz | hz)
      · rcases hz with ⟨k, rfl⟩
        exact ⟨2 * k, by simp only [adversarialTrace, presented_two_mul]⟩
      · exact hz.1

lemma later_presented_ne (gen : FeedbackGenerator) {s t : ℕ} (hst : s < t) :
    (run gen t).presented ≠ (run gen s).presented := by
  by_cases ht : t % 2 = 0
  · by_cases hs : s % 2 = 0
    · rw [presented_even gen ht, presented_even gen hs]
      intro hpow
      have hdiv : t / 2 = s / 2 := core_injective hpow
      omega
    · have hsordinary := presented_odd_mem_ordinary gen hs
      have htcore : (run gen t).presented ∈ core := by
        rw [presented_even gen ht]
        exact ⟨t / 2, rfl⟩
      exact fun heq => hsordinary (heq ▸ htcore)
  · exact future_odd_ne_presented gen hst ht

lemma adversarial_presentation_injective (gen : FeedbackGenerator) :
    Function.Injective (adversarialTrace gen).presentation := by
  intro s t heq
  rcases lt_trichotomy s t with hst | hst | hts
  · exact (later_presented_ne gen hst heq.symm).elim
  · exact hst
  · exact (later_presented_ne gen hts heq).elim

lemma adversarial_clean (gen : FeedbackGenerator) :
    Clean (adversarialTrace gen).presentation (adversarialTarget gen) := by
  intro t
  exact ⟨t, rfl⟩

lemma adversarial_complete (gen : FeedbackGenerator) :
    Complete (adversarialTrace gen).presentation (adversarialTarget gen) := by
  rintro z ⟨t, rfl⟩
  exact ⟨t, rfl⟩

lemma target_query_iff (gen : FeedbackGenerator) {t z : ℕ}
    (hq : (run gen t).query = some z) :
    z ∈ adversarialTarget gen ↔
      z ∈ core ∨ z = (run gen t).presented ∨
        z ∈ Finset.univ.image (fun i : Fin t => (run gen i.val).presented) := by
  constructor
  · rintro ⟨s, hs⟩
    change (run gen s).presented = z at hs
    by_cases hst : s < t
    · exact Or.inr (Or.inr (Finset.mem_image.mpr
        ⟨(⟨s, hst⟩ : Fin t), Finset.mem_univ _, hs⟩))
    · by_cases hts : t < s
      · by_cases hseven : s % 2 = 0
        · left
          rw [← hs, presented_even gen hseven]
          exact ⟨s / 2, rfl⟩
        · exact (future_odd_ne_query gen hts hseven hq hs).elim
      · have : s = t := by omega
        subst s
        exact Or.inr (Or.inl hs.symm)
  · rintro (hz | hz | hz)
    · rcases hz with ⟨k, rfl⟩
      exact ⟨2 * k, by simp only [adversarialTrace, presented_two_mul]⟩
    · exact ⟨t, hz.symm⟩
    · rcases Finset.mem_image.mp hz with ⟨i, -, hi⟩
      refine ⟨i.val, ?_⟩
      change (run gen i.val).presented = z
      exact hi

lemma run_answer_eq (gen : FeedbackGenerator) (t : ℕ) :
    (run gen t).answer = match (run gen t).query with
      | none => none
      | some z => some (membershipAnswer (adversarialTarget gen) z) := by
  rw [run.eq_def]
  dsimp only [Round.answer, Round.query]
  split
  · rfl
  · rename_i z hq
    simp only [membershipAnswer]
    congr 2
    apply propext
    have hqrun : (run gen t).query = some z := by
      rw [run.eq_def]
      exact hq
    convert (target_query_iff gen hqrun).symm using 1
    rw [run.eq_def]

lemma adversarial_follows_protocol (gen : FeedbackGenerator) :
    FollowsProtocol gen (adversarialTarget gen) (adversarialTrace gen) := by
  intro t
  refine ⟨run_query_eq gen t, run_answer_eq gen t, run_output_eq gen t⟩

noncomputable def adversarialPresenter (gen : FeedbackGenerator) : CausalPresenter where
  next t _ _ _ _ := (adversarialTrace gen).presentation t

lemma adversarial_presented_by (gen : FeedbackGenerator) :
    PresentedBy (adversarialPresenter gen) (adversarialTrace gen) := by
  intro t
  rfl

end Stage3Proof

namespace Stage3Proof
open Stage3S2B

lemma core_subset_adversarialTarget (gen : FeedbackGenerator) :
    core ⊆ adversarialTarget gen := by
  rintro z ⟨k, rfl⟩
  exact ⟨2 * k, by simp only [adversarialTrace, presented_two_mul]⟩

lemma adversarialTarget_infinite (gen : FeedbackGenerator) :
    (adversarialTarget gen).Infinite := by
  exact (Set.infinite_range_of_injective core_injective).mono
    (core_subset_adversarialTarget gen)

noncomputable def orderedAdversarial (gen : FeedbackGenerator) : OrderedLanguage where
  carrier := adversarialTarget gen
  enumeration := Nat.nth (fun z => z ∈ adversarialTarget gen)
  enumeration_injective := Nat.nth_injective (adversarialTarget_infinite gen)
  range_enumeration := Nat.range_nth_of_infinite (adversarialTarget_infinite gen)

lemma orderedAdversarial_inherits (gen : FeedbackGenerator) :
    InheritsAmbientOrder (orderedAdversarial gen) := by
  exact Nat.nth_strictMono (adversarialTarget_infinite gen)

noncomputable def earlyOutputs (gen : FeedbackGenerator) (T : ℕ) : Finset ℕ :=
  Finset.univ.image (fun i : Fin T => (run gen i.val).output)

def earlySet (gen : FeedbackGenerator) (T : ℕ) : Set ℕ :=
  {z | z ∈ earlyOutputs gen T}

lemma earlyOutputs_card_le (gen : FeedbackGenerator) (T : ℕ) :
    (earlyOutputs gen T).card ≤ T := by
  unfold earlyOutputs
  simpa using (Finset.card_image_le
    (s := (Finset.univ : Finset (Fin T)))
    (f := fun i : Fin T => (run gen i.val).output))

lemma scored_subset_core_union_early (gen : FeedbackGenerator)
    (hgen : UniversallyEventuallyValidFresh gen) :
    ∃ T, scored (adversarialTarget gen) (adversarialTrace gen).presentation
        (adversarialTrace gen).output ⊆
      core ∪ earlySet gen T := by
  rcases hgen (adversarialTarget gen) (adversarialTarget_mem gen)
      (adversarialTrace gen) (adversarial_follows_protocol gen)
      (adversarial_clean gen) (adversarial_presentation_injective gen)
      (adversarial_complete gen) with ⟨T, hT⟩
  refine ⟨T, ?_⟩
  rintro z ⟨hzK, t, hyt, hfresh⟩
  by_cases ht : T ≤ t
  · left
    by_contra hzcore
    rcases hzK with ⟨s, hs⟩
    change (run gen s).presented = z at hs
    have hlate : t < s := by
      by_contra hnot
      apply hfresh
      exact ⟨s, by omega, by simpa only [adversarialTrace] using hs⟩
    have hsodd : s % 2 ≠ 0 := by
      intro hseven
      apply hzcore
      rw [← hs, presented_even gen hseven]
      exact ⟨s / 2, rfl⟩
    have hne := future_odd_ne_output gen hlate hsodd
    apply hne
    change (run gen s).presented = (run gen t).output
    exact hs.trans hyt.symm
  · right
    unfold earlySet earlyOutputs
    exact Finset.mem_image.mpr
      ⟨(⟨t, by omega⟩ : Fin T), Finset.mem_univ _, by simpa only [adversarialTrace] using hyt⟩

lemma odd_value_bound (gen : FeedbackGenerator) {k n : ℕ} (hkn : k ≤ n) :
    (run gen (2 * k + 1)).presented ≤ 12 * n + 9 := by
  have h := presented_odd_bound gen (t := 2 * k + 1) (by omega)
  omega

lemma orderedAdversarial_enumeration_le (gen : FeedbackGenerator) (n : ℕ) :
    (orderedAdversarial gen).enumeration n ≤ 12 * n + 9 := by
  classical
  let values : Finset ℕ :=
    (Finset.range (n + 1)).image (fun k => (run gen (2 * k + 1)).presented)
  have hinj : Function.Injective
      (fun k => (run gen (2 * k + 1)).presented) := by
    intro a b hab
    have htime := adversarial_presentation_injective gen hab
    omega
  have hcard : values.card = n + 1 := by
    simp [values, Finset.card_image_of_injective _ hinj]
  have hsubset : values ⊆
      (Finset.range (12 * n + 10)).filter
        (fun z => z ∈ adversarialTarget gen) := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨k, hk, rfl⟩
    have hklt := Finset.mem_range.mp hk
    have hkn : k ≤ n := by omega
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr ?_, ?_⟩
    · exact Nat.lt_succ_of_le (odd_value_bound gen hkn)
    · exact ⟨2 * k + 1, rfl⟩
  have hcount : n < Nat.count (fun z => z ∈ adversarialTarget gen) (12 * n + 10) := by
    rw [Nat.count_eq_card_filter_range]
    have := Finset.card_le_card hsubset
    omega
  exact Nat.le_of_lt_succ (Nat.nth_lt_of_lt_count hcount)

end Stage3Proof

namespace Stage3Proof
open Stage3S2B
open GenLimit.KleinbergWei

lemma core_prefixCount_le (gen : FeedbackGenerator) (n : ℕ) :
    (orderedAdversarial gen).prefixCount core n ≤
      Nat.log 2 (12 * n + 9) + 1 := by
  classical
  let selected := (Finset.range n).filter
    (fun i => (orderedAdversarial gen).enumeration i ∈ core)
  have hinj : Set.InjOn
      (fun i => Nat.log 2 ((orderedAdversarial gen).enumeration i)) selected := by
    intro i hi j hj hij
    have hicore := (Finset.mem_filter.mp hi).2
    have hjcore := (Finset.mem_filter.mp hj).2
    rcases hicore with ⟨ki, hki⟩
    rcases hjcore with ⟨kj, hkj⟩
    have hk : ki = kj := by
      simpa only [← hki, ← hkj, Nat.log_pow (by omega : 1 < 2)] using hij
    apply (orderedAdversarial gen).enumeration_injective
    rw [← hki, ← hkj, hk]
  have hmaps : Set.MapsTo
      (fun i => Nat.log 2 ((orderedAdversarial gen).enumeration i)) selected
      (Finset.range (Nat.log 2 (12 * n + 9) + 1)) := by
    intro i hi
    have hiltn := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
    have hicore := (Finset.mem_filter.mp hi).2
    rcases hicore with ⟨k, hk⟩
    have henum := orderedAdversarial_enumeration_le gen i
    have hpow : 2 ^ k ≤ 12 * n + 9 := by
      calc
        2 ^ k = (orderedAdversarial gen).enumeration i := hk
        _ ≤ 12 * i + 9 := henum
        _ ≤ 12 * n + 9 := by omega
    have hklog : k ≤ Nat.log 2 (12 * n + 9) :=
      Nat.le_log_of_pow_le (by omega) hpow
    apply Finset.mem_range.mpr
    simpa only [← hk, Nat.log_pow (by omega : 1 < 2)] using Nat.lt_succ_of_le hklog
  change selected.card ≤ Nat.log 2 (12 * n + 9) + 1
  simpa using Finset.card_le_card_of_injOn _ hmaps hinj

lemma early_prefixCount_le (gen : FeedbackGenerator) (T n : ℕ) :
    (orderedAdversarial gen).prefixCount (earlySet gen T) n ≤ T := by
  classical
  rw [GenLimit.KleinbergWei.OrderedLanguage.prefixCount]
  refine (Finset.card_le_card_of_injOn
    (s := (Finset.range n).filter
      (fun i => (orderedAdversarial gen).enumeration i ∈ earlySet gen T))
    (t := earlyOutputs gen T)
    (orderedAdversarial gen).enumeration ?_
      (orderedAdversarial gen).enumeration_injective.injOn).trans
        (earlyOutputs_card_le gen T)
  intro i hi
  simpa only [earlySet, Set.mem_setOf_eq] using (Finset.mem_filter.mp hi).2

lemma prefixCount_mono (K : Stage3S2B.OrderedLanguage) {A B : Set ℕ} (hAB : A ⊆ B) (n : ℕ) :
    K.prefixCount A n ≤ K.prefixCount B n := by
  classical
  rw [GenLimit.KleinbergWei.OrderedLanguage.prefixCount, GenLimit.KleinbergWei.OrderedLanguage.prefixCount]
  apply Finset.card_le_card
  intro i hi
  exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hi).1,
    hAB (Finset.mem_filter.mp hi).2⟩

lemma prefixCount_union_le (K : Stage3S2B.OrderedLanguage) (A B : Set ℕ) (n : ℕ) :
    K.prefixCount (A ∪ B) n ≤ K.prefixCount A n + K.prefixCount B n := by
  classical
  simp only [GenLimit.KleinbergWei.OrderedLanguage.prefixCount, Set.mem_union]
  rw [Finset.filter_or]
  exact Finset.card_union_le _ _

lemma scored_prefixCount_le (gen : FeedbackGenerator) (T n : ℕ)
    (hsubset : scored (adversarialTarget gen) (adversarialTrace gen).presentation
        (adversarialTrace gen).output ⊆
      core ∪ earlySet gen T) :
    (orderedAdversarial gen).prefixCount
        (scored (adversarialTarget gen) (adversarialTrace gen).presentation
          (adversarialTrace gen).output) n ≤
      Nat.log 2 (12 * n + 9) + 1 + T := by
  calc
    _ ≤ (orderedAdversarial gen).prefixCount
        (core ∪ (earlySet gen T)) n :=
      prefixCount_mono (orderedAdversarial gen) hsubset n
    _ ≤ (orderedAdversarial gen).prefixCount core n +
        (orderedAdversarial gen).prefixCount (earlySet gen T) n :=
      prefixCount_union_le (orderedAdversarial gen) core
        (earlySet gen T) n
    _ ≤ _ := Nat.add_le_add (core_prefixCount_le gen n) (early_prefixCount_le gen T n)

end Stage3Proof

namespace Stage3Proof
open Stage3S2B
open GenLimit.KleinbergWei
open Asymptotics

lemma logarithmic_bound_ratio_tendsto_zero (T : ℕ) :
    Tendsto (fun n : ℕ =>
      ((Nat.log 2 (12 * n + 9) + 1 + T : ℕ) : ℝ) / (n : ℝ))
      atTop (𝓝 0) := by
  let affine : ℕ → ℝ := fun n => ((12 * n + 9 : ℕ) : ℝ)
  have haffine : Tendsto affine atTop atTop := by
    apply tendsto_atTop_mono (f := fun n : ℕ => (n : ℝ))
      (g := affine) (l := atTop)
    · intro n
      dsimp only [affine]
      exact_mod_cast (show n ≤ 12 * n + 9 by omega)
    · exact tendsto_natCast_atTop_atTop
  have hlogAffine : Tendsto (fun n => Real.log (affine n) / affine n)
      atTop (𝓝 0) := by
    simpa only [Function.comp_apply, id_eq] using
      (Real.isLittleO_log_id_atTop.comp_tendsto haffine).tendsto_div_nhds_zero
  have haffineRatio : Tendsto (fun n : ℕ => affine n / (n : ℝ))
      atTop (𝓝 12) := by
    have h := (tendsto_const_div_atTop_nhds_zero_nat 9).const_add (12 : ℝ)
    simpa only [add_zero] using h.congr' (by
      filter_upwards [eventually_ne_atTop (0 : ℕ)] with n hn
      dsimp only [affine]
      push_cast
      field_simp)
  have hlogRatio : Tendsto (fun n : ℕ => Real.log (affine n) / (n : ℝ))
      atTop (𝓝 0) := by
    have h : Tendsto (fun n =>
        (Real.log (affine n) / affine n) * (affine n / (n : ℝ)))
        atTop (𝓝 0) := by
      simpa only [zero_mul] using hlogAffine.mul haffineRatio
    apply h.congr'
    filter_upwards [eventually_ne_atTop (0 : ℕ)] with n hn
    have haffine_ne : affine n ≠ 0 := by
      dsimp only [affine]
      positivity
    field_simp
  have hlogbRatio : Tendsto (fun n : ℕ => Real.logb 2 (affine n) / (n : ℝ))
      atTop (𝓝 0) := by
    have h := hlogRatio.const_mul (1 / Real.log 2)
    convert h using 1
    · funext n
      rw [Real.logb]
      ring
    · ring
  have hrealBound : Tendsto (fun n : ℕ =>
      (Real.logb 2 (affine n) + 1 + T) / (n : ℝ)) atTop (𝓝 0) := by
    have hconstant := tendsto_const_div_atTop_nhds_zero_nat ((1 : ℝ) + T)
    have h := hlogbRatio.add hconstant
    convert h using 1
    · funext n
      ring
    · ring
  apply tendsto_const_nhds.squeeze hrealBound
  · intro n
    positivity
  · intro n
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
    dsimp only [affine]
    push_cast
    gcongr
    simpa only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_mul] using
      Real.natLog_le_logb (12 * n + 9) 2

lemma adversarial_prefixRatio_tendsto_zero (gen : FeedbackGenerator) (T : ℕ)
    (hsubset : scored (adversarialTarget gen) (adversarialTrace gen).presentation
        (adversarialTrace gen).output ⊆ core ∪ earlySet gen T) :
    Tendsto (fun n => (orderedAdversarial gen).prefixRatio
      (scored (adversarialTarget gen) (adversarialTrace gen).presentation
        (adversarialTrace gen).output) n) atTop (𝓝 0) := by
  apply tendsto_const_nhds.squeeze (logarithmic_bound_ratio_tendsto_zero T)
  · intro n
    simp only [GenLimit.KleinbergWei.OrderedLanguage.prefixRatio]
    split
    · exact le_rfl
    · positivity
  · intro n
    simp only [GenLimit.KleinbergWei.OrderedLanguage.prefixRatio]
    split
    · rename_i hn
      simp [hn]
    · apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
      exact_mod_cast scored_prefixCount_le gen T n hsubset

lemma adversarial_upperDensity_zero (gen : FeedbackGenerator) (T : ℕ)
    (hsubset : scored (adversarialTarget gen) (adversarialTrace gen).presentation
        (adversarialTrace gen).output ⊆ core ∪ earlySet gen T) :
    (orderedAdversarial gen).upperDensity
      (scored (adversarialTarget gen) (adversarialTrace gen).presentation
        (adversarialTrace gen).output) = 0 := by
  rw [GenLimit.KleinbergWei.OrderedLanguage.upperDensity]
  exact (adversarial_prefixRatio_tendsto_zero gen T hsubset).limsup_eq

end Stage3Proof

namespace Stage3Proof
open Stage3S2B

lemma negative_claim : NegativeClaim := by
  intro gen hgen
  rcases scored_subset_core_union_early gen hgen with ⟨T, hsubset⟩
  refine ⟨adversarialTarget gen, adversarialTarget_mem gen,
    adversarialPresenter gen, adversarialTrace gen, orderedAdversarial gen, ?_⟩
  exact ⟨rfl, orderedAdversarial_inherits gen, adversarial_presented_by gen,
    adversarial_follows_protocol gen, adversarial_clean gen,
    adversarial_presentation_injective gen, adversarial_complete gen,
    adversarial_upperDensity_zero gen T hsubset⟩

end Stage3Proof
