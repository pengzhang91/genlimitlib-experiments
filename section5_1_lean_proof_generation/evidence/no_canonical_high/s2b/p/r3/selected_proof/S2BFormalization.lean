import Stage3Model
import Mathlib.Data.Nat.Nth
import Mathlib.Analysis.SpecialFunctions.Log.Base

open Set Filter

namespace Stage3S2BProof

open Stage3S2B

private def coding (A : Set ℕ) : Language :=
  core ∪ {z | ∃ n ∈ A, z = 2 * n + 3}

private lemma odd_code_not_core (n : ℕ) : 2 * n + 3 ∉ core := by
  rintro ⟨k, hk⟩
  have hodd : Odd (2 * n + 3) := by
    exact ⟨n + 1, by omega⟩
  have hk0 : k = 0 := by
    by_contra hne
    have heven : Even (2 ^ k) := Even.pow_of_ne_zero even_two hne
    exact (Nat.not_even_iff_odd.mpr hodd) (hk ▸ heven)
  subst k
  norm_num at hk

private lemma coding_ordinary (A : Set ℕ) :
    {z | ∃ n ∈ A, z = 2 * n + 3} ⊆ ordinary := by
  rintro z ⟨n, hn, rfl⟩
  exact odd_code_not_core n

private lemma coding_mem_targetClass (A : Set ℕ) : coding A ∈ targetClass := by
  exact ⟨_, coding_ordinary A, rfl⟩

private lemma coding_injective : Function.Injective coding := by
  intro A B hab
  ext n
  have hncore : 2 * n + 3 ∉ core := odd_code_not_core n
  have hA : 2 * n + 3 ∈ coding A ↔ n ∈ A := by
    simp only [coding, mem_union, hncore, false_or, mem_setOf_eq]
    constructor
    · rintro ⟨m, hm, hmn⟩
      have : m = n := by omega
      simpa [this] using hm
    · intro hn
      exact ⟨n, hn, rfl⟩
  have hncoreB : 2 * n + 3 ∉ core := odd_code_not_core n
  have hB : 2 * n + 3 ∈ coding B ↔ n ∈ B := by
    simp only [coding, mem_union, hncoreB, false_or, mem_setOf_eq]
    constructor
    · rintro ⟨m, hm, hmn⟩
      have : m = n := by omega
      simpa [this] using hm
    · intro hn
      exact ⟨n, hn, rfl⟩
  rw [← hA, hab, hB]

private lemma targetClass_uncountable : ¬ targetClass.Countable := by
  intro hcount
  let f : Set ℕ → targetClass := fun A => ⟨coding A, coding_mem_targetClass A⟩
  have hf : Function.Injective f := by
    intro A B h
    exact coding_injective (congrArg Subtype.val h)
  letI : Countable targetClass := hcount.to_subtype
  haveI : Countable (Set ℕ) := hf.countable
  rcases (countable_iff_exists_surjective.mp (inferInstance : Countable (Set ℕ))) with ⟨e, he⟩
  let D : Set ℕ := {n | n ∉ e n}
  rcases he D with ⟨n, hn⟩
  have hdiag := Set.ext_iff.mp hn n
  simp [D] at hdiag

private lemma pow_two_injective : Function.Injective (fun k : ℕ => 2 ^ k) := by
  exact Nat.pow_right_injective (by omega)

private lemma uniform_generation : UniformlyGeneratableWithoutSamples := by
  refine ⟨fun k => 2 ^ k, pow_two_injective, 0, ?_⟩
  intro K hK t ht
  rcases hK with ⟨A, hA, rfl⟩
  exact Or.inl ⟨t, rfl⟩


private structure History (t : ℕ) where
  presentation : Fin t → ℕ
  query : Fin t → Option ℕ
  answer : Fin t → Option Bool
  output : Fin t → ℕ

private def Safe {t : ℕ} (h : History t) (z : ℕ) : Prop :=
  (∀ i, z ≠ h.presentation i) ∧
    (z ∈ core ∨ ((∀ i, h.query i ≠ some z) ∧ ∀ i, h.output i ≠ z))

private lemma safe_exists {t : ℕ} (h : History t) : ∃ z, Safe h z := by
  let S := ∑ i, h.presentation i
  refine ⟨2 ^ (S + 1), ?_, Or.inl ⟨S + 1, rfl⟩⟩
  intro i hi
  have hle : h.presentation i ≤ S := Finset.single_le_sum
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have hlt : S < 2 ^ (S + 1) := by
    exact lt_of_lt_of_le (Nat.lt_two_pow_self) (Nat.pow_le_pow_right (by omega) (by omega))
  exact (hle.trans_lt hlt).ne' hi

private noncomputable def nextPresentation {t : ℕ} (h : History t) : ℕ := by
  classical
  exact Nat.find (safe_exists h)

private lemma nextPresentation_safe {t : ℕ} (h : History t) :
    Safe h (nextPresentation h) := by
  classical
  exact Nat.find_spec (safe_exists h)

private noncomputable def extend (gen : FeedbackGenerator) {t : ℕ}
    (h : History t) : History (t + 1) := by
  let x := nextPresentation h
  let xs : Fin (t + 1) → ℕ := Fin.lastCases x h.presentation
  let q := gen.query t xs h.answer
  let a := match q with
    | none => none
    | some z => some (membershipAnswer (core ∪ Set.range xs) z)
  let as : Fin (t + 1) → Option Bool := Fin.lastCases a h.answer
  let y := gen.output t xs as
  exact {
    presentation := xs
    query := Fin.lastCases q h.query
    answer := as
    output := Fin.lastCases y h.output
  }

private noncomputable def histories (gen : FeedbackGenerator) : (t : ℕ) → History t
  | 0 => ⟨Fin.elim0, Fin.elim0, Fin.elim0, Fin.elim0⟩
  | t + 1 => extend gen (histories gen t)

private noncomputable def adversarialTranscript (gen : FeedbackGenerator) : Transcript where
  presentation t := (histories gen (t + 1)).presentation (Fin.last t)
  query t := (histories gen (t + 1)).query (Fin.last t)
  answer t := (histories gen (t + 1)).answer (Fin.last t)
  output t := (histories gen (t + 1)).output (Fin.last t)



private lemma histories_succ_presentation_last (gen : FeedbackGenerator) (t : ℕ) :
    (histories gen (t + 1)).presentation (Fin.last t) =
      nextPresentation (histories gen t) := by
  simp [histories, extend]

private lemma histories_succ_presentation_cast (gen : FeedbackGenerator) (t : ℕ) (i : Fin t) :
    (histories gen (t + 1)).presentation i.castSucc =
      (histories gen t).presentation i := by
  simp [histories, extend]

private lemma histories_succ_query_last (gen : FeedbackGenerator) (t : ℕ) :
    (histories gen (t + 1)).query (Fin.last t) =
      gen.query t (histories gen (t + 1)).presentation
        (histories gen t).answer := by
  simp [histories, extend]

private lemma histories_succ_answer_last (gen : FeedbackGenerator) (t : ℕ) :
    (histories gen (t + 1)).answer (Fin.last t) =
      match (histories gen (t + 1)).query (Fin.last t) with
      | none => none
      | some z => some (membershipAnswer
          (core ∪ Set.range (histories gen (t + 1)).presentation) z) := by
  simp [histories, extend]

private lemma histories_succ_output_last (gen : FeedbackGenerator) (t : ℕ) :
    (histories gen (t + 1)).output (Fin.last t) =
      gen.output t (histories gen (t + 1)).presentation
        (histories gen (t + 1)).answer := by
  simp [histories, extend]

private lemma histories_succ_query_cast (gen : FeedbackGenerator) (t : ℕ) (i : Fin t) :
    (histories gen (t + 1)).query i.castSucc = (histories gen t).query i := by
  simp [histories, extend]

private lemma histories_succ_answer_cast (gen : FeedbackGenerator) (t : ℕ) (i : Fin t) :
    (histories gen (t + 1)).answer i.castSucc = (histories gen t).answer i := by
  simp [histories, extend]

private lemma histories_succ_output_cast (gen : FeedbackGenerator) (t : ℕ) (i : Fin t) :
    (histories gen (t + 1)).output i.castSucc = (histories gen t).output i := by
  simp [histories, extend]


private lemma transcript_presentation_prefix (gen : FeedbackGenerator) :
    ∀ (t : ℕ) (i : Fin t),
      (adversarialTranscript gen).presentation i = (histories gen t).presentation i := by
  intro t
  induction t with
  | zero =>
      intro i
      exact Fin.elim0 i
  | succ t ih =>
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rfl
      · rw [histories_succ_presentation_cast]
        exact ih j

private lemma transcript_query_prefix (gen : FeedbackGenerator) :
    ∀ (t : ℕ) (i : Fin t),
      (adversarialTranscript gen).query i = (histories gen t).query i := by
  intro t
  induction t with
  | zero =>
      intro i
      exact Fin.elim0 i
  | succ t ih =>
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rfl
      · rw [histories_succ_query_cast]
        exact ih j

private lemma transcript_answer_prefix (gen : FeedbackGenerator) :
    ∀ (t : ℕ) (i : Fin t),
      (adversarialTranscript gen).answer i = (histories gen t).answer i := by
  intro t
  induction t with
  | zero =>
      intro i
      exact Fin.elim0 i
  | succ t ih =>
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rfl
      · rw [histories_succ_answer_cast]
        exact ih j

private lemma transcript_output_prefix (gen : FeedbackGenerator) :
    ∀ (t : ℕ) (i : Fin t),
      (adversarialTranscript gen).output i = (histories gen t).output i := by
  intro t
  induction t with
  | zero =>
      intro i
      exact Fin.elim0 i
  | succ t ih =>
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rfl
      · rw [histories_succ_output_cast]
        exact ih j


private lemma safe_of_extend {t : ℕ} (gen : FeedbackGenerator) (h : History t) {z : ℕ}
    (hz : Safe (extend gen h) z) : Safe h z := by
  rcases hz with ⟨hzp, hzcore | hzordinary⟩
  · exact ⟨fun i hi => hzp i.castSucc (by simpa [extend] using hi), Or.inl hzcore⟩
  · refine ⟨fun i hi => hzp i.castSucc (by simpa [extend] using hi), Or.inr ⟨?_, ?_⟩⟩
    · intro i hi
      exact hzordinary.1 i.castSucc (by simpa [extend] using hi)
    · intro i hi
      exact hzordinary.2 i.castSucc (by simpa [extend] using hi)

private lemma nextPresentation_lt_next (gen : FeedbackGenerator) {t : ℕ} (h : History t) :
    nextPresentation h < nextPresentation (extend gen h) := by
  classical
  let z := nextPresentation (extend gen h)
  have hzext : Safe (extend gen h) z := nextPresentation_safe _
  have hz : Safe h z := safe_of_extend gen h hzext
  have hle : nextPresentation h ≤ z := Nat.find_min' (safe_exists h) hz
  have hne : z ≠ nextPresentation h := by
    have hlast := hzext.1 (Fin.last t)
    simpa [extend] using hlast
  exact lt_of_le_of_ne hle hne.symm

private lemma transcript_strictMono (gen : FeedbackGenerator) :
    StrictMono (adversarialTranscript gen).presentation := by
  apply strictMono_nat_of_lt_succ
  intro t
  rw [show (adversarialTranscript gen).presentation t =
      nextPresentation (histories gen t) from histories_succ_presentation_last gen t]
  rw [show (adversarialTranscript gen).presentation (t + 1) =
      nextPresentation (histories gen (t + 1)) from
        histories_succ_presentation_last gen (t + 1)]
  simpa [histories] using nextPresentation_lt_next gen (histories gen t)


private lemma core_subset_presentation_range (gen : FeedbackGenerator) :
    core ⊆ Set.range (adversarialTranscript gen).presentation := by
  intro z hzcore
  by_contra hzrange
  have hsafe : Safe (histories gen (z + 1)) z := by
    refine ⟨?_, Or.inl hzcore⟩
    intro i hi
    apply hzrange
    refine ⟨i, ?_⟩
    rw [transcript_presentation_prefix gen (z + 1) i]
    exact hi.symm
  have hle : nextPresentation (histories gen (z + 1)) ≤ z := by
    classical
    exact Nat.find_min' (safe_exists _) hsafe
  have hid : z + 1 ≤ (adversarialTranscript gen).presentation (z + 1) :=
    (transcript_strictMono gen).id_le (z + 1)
  rw [show (adversarialTranscript gen).presentation (z + 1) =
      nextPresentation (histories gen (z + 1)) from
        histories_succ_presentation_last gen (z + 1)] at hid
  omega

private def adversarialTarget (gen : FeedbackGenerator) : Language :=
  Set.range (adversarialTranscript gen).presentation

private lemma adversarialTarget_mem (gen : FeedbackGenerator) :
    adversarialTarget gen ∈ targetClass := by
  let A := adversarialTarget gen ∩ ordinary
  refine ⟨A, inter_subset_right, ?_⟩
  ext z
  constructor
  · intro hz
    by_cases hc : z ∈ core
    · exact Or.inl hc
    · exact Or.inr ⟨hz, hc⟩
  · rintro (hc | ⟨hz, ho⟩)
    · exact core_subset_presentation_range gen hc
    · exact hz

private lemma adversarial_clean (gen : FeedbackGenerator) :
    Clean (adversarialTranscript gen).presentation (adversarialTarget gen) := by
  intro t
  exact ⟨t, rfl⟩

private lemma adversarial_complete (gen : FeedbackGenerator) :
    Complete (adversarialTranscript gen).presentation (adversarialTarget gen) := by
  intro z hz
  exact hz

private lemma adversarial_injective (gen : FeedbackGenerator) :
    Function.Injective (adversarialTranscript gen).presentation :=
  (transcript_strictMono gen).injective

private noncomputable def adversarialPresenter (gen : FeedbackGenerator) : CausalPresenter where
  next t _ _ _ _ := (adversarialTranscript gen).presentation t

private lemma adversarial_presentedBy (gen : FeedbackGenerator) :
    PresentedBy (adversarialPresenter gen) (adversarialTranscript gen) := by
  intro t
  rfl


private lemma future_presentation_ne_of_query (gen : FeedbackGenerator) {t s z : ℕ}
    (hts : t < s) (hq : (adversarialTranscript gen).query t = some z)
    (hz : z ∉ core) : (adversarialTranscript gen).presentation s ≠ z := by
  intro hs
  have hsafe := nextPresentation_safe (histories gen s)
  rw [show (adversarialTranscript gen).presentation s = nextPresentation (histories gen s) from
    histories_succ_presentation_last gen s] at hs
  have hnotcore : nextPresentation (histories gen s) ∉ core := by simpa [hs] using hz
  rcases hsafe.2 with hc | ho
  · exact hnotcore hc
  · let i : Fin s := ⟨t, hts⟩
    have hqi := ho.1 i
    rw [← transcript_query_prefix gen s i] at hqi
    exact hqi (by simpa [hs] using hq)

private lemma future_presentation_ne_of_output (gen : FeedbackGenerator) {t s z : ℕ}
    (hts : t < s) (hy : (adversarialTranscript gen).output t = z)
    (hz : z ∉ core) : (adversarialTranscript gen).presentation s ≠ z := by
  intro hs
  have hsafe := nextPresentation_safe (histories gen s)
  rw [show (adversarialTranscript gen).presentation s = nextPresentation (histories gen s) from
    histories_succ_presentation_last gen s] at hs
  have hnotcore : nextPresentation (histories gen s) ∉ core := by simpa [hs] using hz
  rcases hsafe.2 with hc | ho
  · exact hnotcore hc
  · let i : Fin s := ⟨t, hts⟩
    have hyi := ho.2 i
    rw [← transcript_output_prefix gen s i] at hyi
    exact hyi (by simpa [hs] using hy)

private lemma queried_membership_current_iff_target (gen : FeedbackGenerator) (t z : ℕ)
    (hq : (adversarialTranscript gen).query t = some z) :
    z ∈ core ∪ Set.range (histories gen (t + 1)).presentation ↔
      z ∈ adversarialTarget gen := by
  constructor
  · rintro (hc | ⟨i, hi⟩)
    · exact core_subset_presentation_range gen hc
    · refine ⟨i, ?_⟩
      rw [transcript_presentation_prefix gen (t + 1) i]
      exact hi
  · rintro ⟨s, hs⟩
    by_cases hc : z ∈ core
    · exact Or.inl hc
    · right
      by_cases hst : s ≤ t
      · let i : Fin (t + 1) := ⟨s, by omega⟩
        refine ⟨i, ?_⟩
        rw [← transcript_presentation_prefix gen (t + 1) i]
        exact hs
      · exact False.elim (future_presentation_ne_of_query gen (Nat.lt_of_not_ge hst) hq hc hs)

private lemma adversarial_protocol (gen : FeedbackGenerator) :
    FollowsProtocol gen (adversarialTarget gen) (adversarialTranscript gen) := by
  intro t
  have hq : (adversarialTranscript gen).query t =
      gen.query t (fun i => (adversarialTranscript gen).presentation i)
        (fun i => (adversarialTranscript gen).answer i) := by
    rw [show (adversarialTranscript gen).query t =
      gen.query t (histories gen (t + 1)).presentation (histories gen t).answer from
        histories_succ_query_last gen t]
    congr 1
    · funext i
      exact (transcript_presentation_prefix gen (t + 1) i).symm
    · funext i
      exact (transcript_answer_prefix gen t i).symm
  refine ⟨hq, ?_, ?_⟩
  · rw [show (adversarialTranscript gen).answer t =
      match (adversarialTranscript gen).query t with
      | none => none
      | some z => some (membershipAnswer
          (core ∪ Set.range (histories gen (t + 1)).presentation) z) from
        histories_succ_answer_last gen t]
    cases hqt : (adversarialTranscript gen).query t with
    | none => rfl
    | some z =>
        apply congrArg some
        apply Bool.eq_iff_iff.mpr
        simp only [membershipAnswer, decide_eq_true_eq]
        exact queried_membership_current_iff_target gen t z hqt
  · rw [show (adversarialTranscript gen).output t =
      gen.output t (histories gen (t + 1)).presentation
        (histories gen (t + 1)).answer from histories_succ_output_last gen t]
    congr 1
    · funext i
      exact (transcript_presentation_prefix gen (t + 1) i).symm
    · funext i
      exact (transcript_answer_prefix gen (t + 1) i).symm


private lemma nextPresentation_le (h : History t) : nextPresentation h ≤ 3 * t := by
  classical
  let P : Finset ℕ := Finset.univ.image h.presentation
  let Q : Finset ℕ := Finset.univ.image (fun i => (h.query i).getD 0)
  let Y : Finset ℕ := Finset.univ.image h.output
  let F := P ∪ Q ∪ Y
  have hP : P.card ≤ t := by
    calc
      P.card ≤ (Finset.univ : Finset (Fin t)).card := Finset.card_image_le
      _ = t := by simp
  have hQ : Q.card ≤ t := by
    calc
      Q.card ≤ (Finset.univ : Finset (Fin t)).card := Finset.card_image_le
      _ = t := by simp
  have hY : Y.card ≤ t := by
    calc
      Y.card ≤ (Finset.univ : Finset (Fin t)).card := Finset.card_image_le
      _ = t := by simp
  have hF : F.card ≤ 3 * t := by
    dsimp [F]
    calc
      (P ∪ Q ∪ Y).card ≤ (P ∪ Q).card + Y.card := Finset.card_union_le _ _
      _ ≤ (P.card + Q.card) + Y.card := Nat.add_le_add_right (Finset.card_union_le _ _) _
      _ ≤ 3 * t := by omega
  have hcard : F.card < (Finset.range (3 * t + 1)).card := by simp; omega
  rcases Finset.exists_mem_notMem_of_card_lt_card hcard with ⟨z, hzrange, hzF⟩
  have hzsafe : Safe h z := by
    refine ⟨?_, Or.inr ⟨?_, ?_⟩⟩
    · intro i hi
      apply hzF
      exact Finset.mem_union_left Y
        (Finset.mem_union_left Q (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi.symm⟩))
    · intro i hi
      apply hzF
      exact Finset.mem_union_left Y
        (Finset.mem_union_right P (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, by simp [hi]⟩))
    · intro i hi
      apply hzF
      exact Finset.mem_union_right (P ∪ Q)
        (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩)
  have hfind : nextPresentation h ≤ z := Nat.find_min' (safe_exists h) hzsafe
  exact hfind.trans (by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hzrange))

private lemma transcript_le (gen : FeedbackGenerator) (t : ℕ) :
    (adversarialTranscript gen).presentation t ≤ 3 * t := by
  rw [show (adversarialTranscript gen).presentation t = nextPresentation (histories gen t) from
    histories_succ_presentation_last gen t]
  exact nextPresentation_le _

private noncomputable def orderedTarget (gen : FeedbackGenerator) : OrderedLanguage where
  carrier := adversarialTarget gen
  enumeration := (adversarialTranscript gen).presentation
  enumeration_injective := adversarial_injective gen
  range_enumeration := rfl

private lemma orderedTarget_inherits (gen : FeedbackGenerator) :
    InheritsAmbientOrder (orderedTarget gen) :=
  transcript_strictMono gen

private lemma prefixCount_core_le (gen : FeedbackGenerator) (n : ℕ) :
    (orderedTarget gen).prefixCount core n ≤ Nat.log 2 (3 * n) + 1 := by
  classical
  let S := (Finset.range n).filter fun i =>
    (adversarialTranscript gen).presentation i ∈ core
  change S.card ≤ Nat.log 2 (3 * n) + 1
  have hmap : Set.MapsTo
      (fun i => Nat.log 2 ((adversarialTranscript gen).presentation i))
      (S : Set ℕ) (Finset.range (Nat.log 2 (3 * n) + 1) : Set ℕ) := by
    intro i hi
    have hi' := (Finset.mem_filter.mp hi)
    have hin : i < n := Finset.mem_range.mp hi'.1
    have hle : (adversarialTranscript gen).presentation i ≤ 3 * n :=
      (transcript_le gen i).trans (by omega)
    have hlog : Nat.log 2 ((adversarialTranscript gen).presentation i) ≤
        Nat.log 2 (3 * n) := Nat.log_mono_right hle
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le hlog)
  have hinj : Set.InjOn
      (fun i => Nat.log 2 ((adversarialTranscript gen).presentation i)) (S : Set ℕ) := by
    intro i hi j hj hij
    have hicore := (Finset.mem_filter.mp hi).2
    have hjcore := (Finset.mem_filter.mp hj).2
    rcases hicore with ⟨ki, hki⟩
    rcases hjcore with ⟨kj, hkj⟩
    have hk : ki = kj := by
      change Nat.log 2 ((adversarialTranscript gen).presentation i) =
        Nat.log 2 ((adversarialTranscript gen).presentation j) at hij
      rw [← hki, ← hkj, Nat.log_pow (by omega), Nat.log_pow (by omega)] at hij
      exact hij
    apply adversarial_injective gen
    calc
      (adversarialTranscript gen).presentation i = 2 ^ ki := hki.symm
      _ = 2 ^ kj := by rw [hk]
      _ = (adversarialTranscript gen).presentation j := hkj
  simpa using Finset.card_le_card_of_injOn
    (fun i => Nat.log 2 ((adversarialTranscript gen).presentation i)) hmap hinj

private lemma log_bound_tendsto_zero : Tendsto (fun n : ℕ =>
    (Real.logb 2 (3 * n) + 1) / (n : ℝ)) atTop (nhds 0) := by
  have hk : Tendsto (fun n : ℕ => (3 : ℝ) * n) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num)
  have hbase := Real.tendsto_pow_logb_div_mul_add_atTop
    (b := (2 : ℝ)) 1 0 1 one_ne_zero
  have hcomp := hbase.comp hk
  have hlog : Tendsto (fun n : ℕ =>
      Real.logb 2 ((3 : ℝ) * n) / ((3 : ℝ) * n)) atTop (nhds 0) := by
    simpa using hcomp
  have hlog' := hlog.const_mul (3 : ℝ)
  have hone := tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)
  have hadd := hlog'.add hone
  have hadd0 : Tendsto (fun n : ℕ =>
      3 * (Real.logb 2 ((3 : ℝ) * n) / ((3 : ℝ) * n)) + 1 / (n : ℝ))
      atTop (nhds 0) := by simpa using hadd
  apply hadd0.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  norm_num [Nat.cast_mul, hn0]
  field_simp

private lemma prefixRatio_core_nonneg (gen : FeedbackGenerator) (n : ℕ) :
    0 ≤ (orderedTarget gen).prefixRatio core n := by
  simp only [GenLimit.KleinbergWei.OrderedLanguage.prefixRatio]
  split_ifs
  · exact le_rfl
  · positivity

private lemma prefixRatio_core_le_log_bound (gen : FeedbackGenerator) (n : ℕ) :
    (orderedTarget gen).prefixRatio core n ≤
      (Real.logb 2 (3 * n) + 1) / (n : ℝ) := by
  by_cases hn : n = 0
  · subst n
    simp [GenLimit.KleinbergWei.OrderedLanguage.prefixRatio]
  · rw [GenLimit.KleinbergWei.OrderedLanguage.prefixRatio, if_neg hn]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
    calc
      ((orderedTarget gen).prefixCount core n : ℝ) ≤
          (Nat.log 2 (3 * n) + 1 : ℕ) := by
        exact_mod_cast prefixCount_core_le gen n
      _ = (Nat.log 2 (3 * n) : ℝ) + 1 := by norm_num
      _ ≤ Real.logb 2 (3 * n) + 1 := by
        gcongr
        simpa [Nat.cast_mul] using Real.natLog_le_logb (3 * n) 2

private lemma prefixRatio_core_tendsto_zero (gen : FeedbackGenerator) :
    Tendsto ((orderedTarget gen).prefixRatio core) atTop (nhds 0) := by
  exact squeeze_zero (prefixRatio_core_nonneg gen)
    (prefixRatio_core_le_log_bound gen) log_bound_tendsto_zero

private lemma upperDensity_core_zero (gen : FeedbackGenerator) :
    (orderedTarget gen).upperDensity core = 0 := by
  exact (prefixRatio_core_tendsto_zero gen).limsup_eq

private lemma scored_subset_core (gen : FeedbackGenerator) :
    scored (adversarialTarget gen) (adversarialTranscript gen).presentation
      (adversarialTranscript gen).output ⊆ core := by
  rintro z ⟨hzK, t, hyt, hzobs⟩
  by_contra hzcore
  rcases hzK with ⟨s, hxs⟩
  have hts : t < s := by
    by_contra hst
    apply hzobs
    exact ⟨s, Nat.le_of_not_gt hst, hxs⟩
  exact future_presentation_ne_of_output gen hts hyt hzcore hxs

private lemma prefixCount_mono (K : OrderedLanguage) {A B : Language}
    (hAB : A ⊆ B) (n : ℕ) : K.prefixCount A n ≤ K.prefixCount B n := by
  classical
  apply Finset.card_le_card
  intro i hi
  have hi' := Finset.mem_filter.mp hi
  exact Finset.mem_filter.mpr ⟨hi'.1, hAB hi'.2⟩

private lemma prefixRatio_mono (K : OrderedLanguage) {A B : Language}
    (hAB : A ⊆ B) (n : ℕ) : K.prefixRatio A n ≤ K.prefixRatio B n := by
  by_cases hn : n = 0
  · subst n
    simp [GenLimit.KleinbergWei.OrderedLanguage.prefixRatio]
  · rw [GenLimit.KleinbergWei.OrderedLanguage.prefixRatio,
      GenLimit.KleinbergWei.OrderedLanguage.prefixRatio, if_neg hn, if_neg hn]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
    exact_mod_cast prefixCount_mono K hAB n

private lemma prefixRatio_scored_tendsto_zero (gen : FeedbackGenerator) :
    Tendsto ((orderedTarget gen).prefixRatio
      (scored (adversarialTarget gen) (adversarialTranscript gen).presentation
        (adversarialTranscript gen).output)) atTop (nhds 0) := by
  apply squeeze_zero
  · intro n
    simp only [GenLimit.KleinbergWei.OrderedLanguage.prefixRatio]
    split_ifs
    · exact le_rfl
    · positivity
  · intro n
    exact prefixRatio_mono (orderedTarget gen) (scored_subset_core gen) n
  · exact prefixRatio_core_tendsto_zero gen

private lemma upperDensity_scored_zero (gen : FeedbackGenerator) :
    (orderedTarget gen).upperDensity
      (scored (adversarialTarget gen) (adversarialTranscript gen).presentation
        (adversarialTranscript gen).output) = 0 := by
  exact (prefixRatio_scored_tendsto_zero gen).limsup_eq

private lemma negative_claim : NegativeClaim := by
  intro gen _
  refine ⟨adversarialTarget gen, adversarialTarget_mem gen,
    adversarialPresenter gen, adversarialTranscript gen, orderedTarget gen, ?_⟩
  exact ⟨rfl, orderedTarget_inherits gen, adversarial_presentedBy gen,
    adversarial_protocol gen, adversarial_clean gen, adversarial_injective gen,
    adversarial_complete gen, upperDensity_scored_zero gen⟩

end Stage3S2BProof

theorem stage3_result : Stage3S2B.MainClaim := by
  exact ⟨Stage3S2BProof.targetClass_uncountable,
    Stage3S2BProof.uniform_generation, Stage3S2BProof.negative_claim⟩
