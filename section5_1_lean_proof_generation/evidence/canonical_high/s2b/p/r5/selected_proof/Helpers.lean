import Stage3Model
import Mathlib.Data.Nat.Nth
import Mathlib.Analysis.SpecialFunctions.Log.Base

open Set Filter

namespace Stage3S2BProof

open Stage3S2B

private def code (n : ℕ) : ℕ := 2 * n + 3

private theorem code_injective : Function.Injective code := by
  intro a b h
  simp only [code] at h
  omega

private theorem code_not_core (n : ℕ) : code n ∉ core := by
  rintro ⟨k, hk⟩
  cases k with
  | zero => simp [code] at hk
  | succ k =>
      simp only [code, pow_succ] at hk
      omega

private def familyMap (A : Set ℕ) : Language := core ∪ code '' A

private theorem familyMap_mem (A : Set ℕ) : familyMap A ∈ targetClass := by
  refine ⟨code '' A, ?_, rfl⟩
  intro z hz
  rcases hz with ⟨n, hn, rfl⟩
  exact code_not_core n

private theorem familyMap_injective : Function.Injective familyMap := by
  intro A B h
  ext n
  have hn : code n ∉ core := code_not_core n
  have hcode := Set.ext_iff.mp h (code n)
  simp only [familyMap, Set.mem_union, Set.mem_image, hn, false_or] at hcode
  constructor
  · intro hA
    rcases hcode.mp ⟨n, hA, rfl⟩ with ⟨m, hm, heq⟩
    rwa [code_injective heq] at hm
  · intro hB
    rcases hcode.mpr ⟨n, hB, rfl⟩ with ⟨m, hm, heq⟩
    rwa [code_injective heq] at hm

theorem targetClass_uncountable : ¬ targetClass.Countable := by
  intro hcount
  have hrange : (Set.range familyMap).Countable := by
    apply hcount.mono
    rintro K ⟨A, rfl⟩
    exact familyMap_mem A
  have hpre := hrange.preimage familyMap_injective
  have huniv : (Set.univ : Set (Set ℕ)).Countable := by
    simpa using hpre
  rcases Set.countable_iff_exists_subset_range.mp huniv with ⟨f, hf⟩
  let diagonal : Set ℕ := {n | n ∉ f n}
  rcases hf (by simp : diagonal ∈ (Set.univ : Set (Set ℕ))) with ⟨n, hn⟩
  have hdiag : n ∈ diagonal ↔ n ∉ diagonal := by
    change n ∉ f n ↔ n ∉ diagonal
    rw [hn]
  by_cases h : n ∈ diagonal
  · exact (hdiag.mp h) h
  · exact h (hdiag.mpr h)

theorem uniform_generation : UniformlyGeneratableWithoutSamples := by
  refine ⟨fun t => 2 ^ t, Nat.pow_right_injective (by omega), 0, ?_⟩
  intro K hK t ht
  rcases hK with ⟨A, hA, rfl⟩
  exact Set.mem_union_left _ ⟨t, rfl⟩

end Stage3S2BProof

namespace Stage3S2BProof

open Stage3S2B

private theorem exists_ordinary_not_mem (F : Finset ℕ) :
    ∃ n, n ∈ ordinary ∧ n ∉ F := by
  rcases Finset.exists_nat_subset_range F with ⟨N, hN⟩
  refine ⟨code N, code_not_core N, ?_⟩
  intro hmem
  have hlt : code N < N := Finset.mem_range.mp (hN hmem)
  simp only [code] at hlt
  omega

noncomputable def freshOrdinary (F : Finset ℕ) : ℕ := by
  classical
  exact Nat.find (exists_ordinary_not_mem F)

theorem freshOrdinary_mem (F : Finset ℕ) : freshOrdinary F ∈ ordinary := by
  classical
  exact (Nat.find_spec (exists_ordinary_not_mem F)).1

theorem freshOrdinary_not_mem (F : Finset ℕ) : freshOrdinary F ∉ F := by
  classical
  exact (Nat.find_spec (exists_ordinary_not_mem F)).2

noncomputable def forbidden {t : ℕ} (p : Fin t → ℕ)
    (q : Fin t → Option ℕ) (y : Fin t → ℕ) : Finset ℕ :=
  (Finset.univ.image p) ∪
    (Finset.univ.biUnion fun i => (q i).toFinset) ∪
    (Finset.univ.image y)

noncomputable def presenterStep (t : ℕ) (p : Fin t → ℕ)
    (q : Fin t → Option ℕ) (_a : Fin t → Option Bool) (y : Fin t → ℕ) : ℕ :=
  if t % 2 = 0 then 2 ^ (t / 2) else freshOrdinary (forbidden p q y)

structure History (t : ℕ) where
  presentation : Fin t → ℕ
  query : Fin t → Option ℕ
  answer : Fin t → Option Bool
  output : Fin t → ℕ

noncomputable def extendHistory (gen : FeedbackGenerator) (t : ℕ)
    (h : History t) : History (t + 1) := by
  let x := presenterStep t h.presentation h.query h.answer h.output
  let p' : Fin (t + 1) → ℕ := Fin.snoc h.presentation x
  let qNow := gen.query t p' h.answer
  let q' : Fin (t + 1) → Option ℕ := Fin.snoc h.query qNow
  let partialTarget : Language := core ∪ Set.range p'
  let aNow := qNow.map (membershipAnswer partialTarget)
  let a' : Fin (t + 1) → Option Bool := Fin.snoc h.answer aNow
  let yNow := gen.output t p' a'
  exact {
    presentation := p'
    query := q'
    answer := a'
    output := Fin.snoc h.output yNow
  }

noncomputable def buildHistory (gen : FeedbackGenerator) : (t : ℕ) → History t
  | 0 => {
      presentation := Fin.elim0
      query := Fin.elim0
      answer := Fin.elim0
      output := Fin.elim0
    }
  | t + 1 => extendHistory gen t (buildHistory gen t)

noncomputable def builtTranscript (gen : FeedbackGenerator) : Transcript where
  presentation t := (buildHistory gen (t + 1)).presentation (Fin.last t)
  query t := (buildHistory gen (t + 1)).query (Fin.last t)
  answer t := (buildHistory gen (t + 1)).answer (Fin.last t)
  output t := (buildHistory gen (t + 1)).output (Fin.last t)

noncomputable def builtPresenter : CausalPresenter where
  next := presenterStep

end Stage3S2BProof

namespace Stage3S2BProof

open Stage3S2B

private theorem build_succ_p (gen : FeedbackGenerator) (t : ℕ) (i : Fin t) :
    (buildHistory gen (t + 1)).presentation i.castSucc =
      (buildHistory gen t).presentation i := by
  simp [buildHistory, extendHistory]

private theorem build_succ_q (gen : FeedbackGenerator) (t : ℕ) (i : Fin t) :
    (buildHistory gen (t + 1)).query i.castSucc =
      (buildHistory gen t).query i := by
  simp [buildHistory, extendHistory]

private theorem build_succ_a (gen : FeedbackGenerator) (t : ℕ) (i : Fin t) :
    (buildHistory gen (t + 1)).answer i.castSucc =
      (buildHistory gen t).answer i := by
  simp [buildHistory, extendHistory]

private theorem build_succ_y (gen : FeedbackGenerator) (t : ℕ) (i : Fin t) :
    (buildHistory gen (t + 1)).output i.castSucc =
      (buildHistory gen t).output i := by
  simp [buildHistory, extendHistory]

private theorem history_p_eq (gen : FeedbackGenerator) (t : ℕ) (i : Fin t) :
    (buildHistory gen t).presentation i = (builtTranscript gen).presentation i.val := by
  induction t with
  | zero => exact Fin.elim0 i
  | succ t ih =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rfl
      · rw [build_succ_p]
        exact ih j

private theorem history_q_eq (gen : FeedbackGenerator) (t : ℕ) (i : Fin t) :
    (buildHistory gen t).query i = (builtTranscript gen).query i.val := by
  induction t with
  | zero => exact Fin.elim0 i
  | succ t ih =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rfl
      · rw [build_succ_q]
        exact ih j

private theorem history_a_eq (gen : FeedbackGenerator) (t : ℕ) (i : Fin t) :
    (buildHistory gen t).answer i = (builtTranscript gen).answer i.val := by
  induction t with
  | zero => exact Fin.elim0 i
  | succ t ih =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rfl
      · rw [build_succ_a]
        exact ih j

private theorem history_y_eq (gen : FeedbackGenerator) (t : ℕ) (i : Fin t) :
    (buildHistory gen t).output i = (builtTranscript gen).output i.val := by
  induction t with
  | zero => exact Fin.elim0 i
  | succ t ih =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rfl
      · rw [build_succ_y]
        exact ih j

end Stage3S2BProof

namespace Stage3S2BProof

open Stage3S2B

private theorem transcript_p_step (gen : FeedbackGenerator) (t : ℕ) :
    (builtTranscript gen).presentation t = presenterStep t
      (buildHistory gen t).presentation (buildHistory gen t).query
      (buildHistory gen t).answer (buildHistory gen t).output := by
  simp [builtTranscript, buildHistory, extendHistory]

private theorem transcript_q_step (gen : FeedbackGenerator) (t : ℕ) :
    (builtTranscript gen).query t = gen.query t
      (buildHistory gen (t + 1)).presentation (buildHistory gen t).answer := by
  simp [builtTranscript, buildHistory, extendHistory]

private theorem transcript_y_step (gen : FeedbackGenerator) (t : ℕ) :
    (builtTranscript gen).output t = gen.output t
      (buildHistory gen (t + 1)).presentation (buildHistory gen (t + 1)).answer := by
  simp [builtTranscript, buildHistory, extendHistory]

private theorem presentation_even (gen : FeedbackGenerator) (t : ℕ)
    (ht : t % 2 = 0) :
    (builtTranscript gen).presentation t = 2 ^ (t / 2) := by
  rw [transcript_p_step]
  simp [presenterStep, ht]

private theorem presentation_odd_mem_ordinary (gen : FeedbackGenerator) (t : ℕ)
    (ht : t % 2 ≠ 0) :
    (builtTranscript gen).presentation t ∈ ordinary := by
  rw [transcript_p_step]
  simp only [presenterStep, ht, if_false]
  exact freshOrdinary_mem _

private theorem history_p_mem_forbidden (gen : FeedbackGenerator) (t : ℕ) (i : Fin t) :
    (buildHistory gen t).presentation i ∈ forbidden
      (buildHistory gen t).presentation (buildHistory gen t).query
      (buildHistory gen t).output := by
  classical
  simp [forbidden]

private theorem presentation_odd_ne_prior (gen : FeedbackGenerator) (t : ℕ)
    (ht : t % 2 ≠ 0) (i : Fin t) :
    (builtTranscript gen).presentation t ≠ (buildHistory gen t).presentation i := by
  rw [transcript_p_step]
  simp only [presenterStep, ht, if_false]
  intro heq
  have hnot := freshOrdinary_not_mem (forbidden
    (buildHistory gen t).presentation (buildHistory gen t).query
    (buildHistory gen t).output)
  apply hnot
  rw [heq]
  exact history_p_mem_forbidden gen t i

private theorem presentation_injective (gen : FeedbackGenerator) :
    Function.Injective (builtTranscript gen).presentation := by
  intro i j hij
  by_contra hne
  wlog hlt : i < j generalizing i j
  · have hji : j < i := Nat.lt_of_le_of_ne (Nat.le_of_not_gt hlt) (Ne.symm hne)
    exact this (Eq.symm hij) (Ne.symm hne) hji
  by_cases hj : j % 2 = 0
  · have hjcore : (builtTranscript gen).presentation j ∈ core := by
      rw [presentation_even gen j hj]
      exact ⟨j / 2, rfl⟩
    by_cases hi : i % 2 = 0
    · rw [presentation_even gen i hi, presentation_even gen j hj] at hij
      have hexp : i / 2 = j / 2 := Nat.pow_right_injective (by omega) hij
      omega
    · have hiord := presentation_odd_mem_ordinary gen i hi
      exact hiord (hij ▸ hjcore)
  · let fi : Fin j := ⟨i, hlt⟩
    have hprior := presentation_odd_ne_prior gen j hj fi
    apply hprior
    rw [history_p_eq]
    exact hij.symm

noncomputable def builtTarget (gen : FeedbackGenerator) : Language :=
  core ∪ Set.range (builtTranscript gen).presentation

private theorem builtTarget_mem_class (gen : FeedbackGenerator) :
    builtTarget gen ∈ targetClass := by
  refine ⟨Set.range (builtTranscript gen).presentation \ core, ?_, ?_⟩
  · intro z hz
    exact hz.2
  · ext z
    simp only [builtTarget, Set.mem_union, Set.mem_range, Set.mem_diff]
    tauto

private theorem built_clean (gen : FeedbackGenerator) :
    Clean (builtTranscript gen).presentation (builtTarget gen) := by
  intro t
  exact Set.mem_union_right _ ⟨t, rfl⟩

private theorem built_complete (gen : FeedbackGenerator) :
    Complete (builtTranscript gen).presentation (builtTarget gen) := by
  intro z hz
  rcases hz with hz | ⟨t, rfl⟩
  · rcases hz with ⟨k, rfl⟩
    refine ⟨2 * k, ?_⟩
    simpa using presentation_even gen (2 * k) (by omega)
  · exact ⟨t, rfl⟩

end Stage3S2BProof

namespace Stage3S2BProof

open Stage3S2B

private theorem history_q_mem_forbidden (gen : FeedbackGenerator) (t : ℕ)
    (i : Fin t) (z : ℕ) (hz : (buildHistory gen t).query i = some z) :
    z ∈ forbidden (buildHistory gen t).presentation (buildHistory gen t).query
      (buildHistory gen t).output := by
  classical
  unfold forbidden
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  apply Finset.mem_biUnion.mpr
  exact ⟨i, Finset.mem_univ i, by simpa using hz⟩

private theorem history_y_mem_forbidden (gen : FeedbackGenerator) (t : ℕ)
    (i : Fin t) :
    (buildHistory gen t).output i ∈ forbidden
      (buildHistory gen t).presentation (buildHistory gen t).query
      (buildHistory gen t).output := by
  classical
  simp [forbidden]

private theorem future_p_ne_query (gen : FeedbackGenerator) {t s z : ℕ}
    (hts : t < s) (hq : (builtTranscript gen).query t = some z)
    (hz : z ∈ ordinary) : (builtTranscript gen).presentation s ≠ z := by
  by_cases hs : s % 2 = 0
  · intro heq
    apply hz
    rw [← heq, presentation_even gen s hs]
    exact ⟨s / 2, rfl⟩
  · rw [transcript_p_step]
    simp only [presenterStep, hs, if_false]
    intro heq
    have hnot := freshOrdinary_not_mem (forbidden
      (buildHistory gen s).presentation (buildHistory gen s).query
      (buildHistory gen s).output)
    apply hnot
    rw [heq]
    let i : Fin s := ⟨t, hts⟩
    apply history_q_mem_forbidden gen s i z
    rw [history_q_eq]
    exact hq

private theorem future_p_ne_output (gen : FeedbackGenerator) {t s : ℕ}
    (hts : t < s) (hz : (builtTranscript gen).output t ∈ ordinary) :
    (builtTranscript gen).presentation s ≠ (builtTranscript gen).output t := by
  by_cases hs : s % 2 = 0
  · intro heq
    apply hz
    rw [← heq, presentation_even gen s hs]
    exact ⟨s / 2, rfl⟩
  · rw [transcript_p_step]
    simp only [presenterStep, hs, if_false]
    intro heq
    have hnot := freshOrdinary_not_mem (forbidden
      (buildHistory gen s).presentation (buildHistory gen s).query
      (buildHistory gen s).output)
    apply hnot
    rw [heq]
    let i : Fin s := ⟨t, hts⟩
    rw [← history_y_eq gen s i]
    exact history_y_mem_forbidden gen s i

private theorem partial_mem_iff_final (gen : FeedbackGenerator) (t z : ℕ)
    (hq : (builtTranscript gen).query t = some z) :
    z ∈ core ∪ Set.range (buildHistory gen (t + 1)).presentation ↔
      z ∈ builtTarget gen := by
  constructor
  · intro hz
    rcases hz with hz | ⟨i, hi⟩
    · exact Set.mem_union_left _ hz
    · right
      refine ⟨i.val, ?_⟩
      rw [← history_p_eq gen (t + 1) i]
      exact hi
  · intro hz
    rcases hz with hz | ⟨s, hs⟩
    · exact Set.mem_union_left _ hz
    · by_cases hst : s ≤ t
      · right
        let i : Fin (t + 1) := ⟨s, by omega⟩
        refine ⟨i, ?_⟩
        rw [history_p_eq]
        exact hs
      · by_cases hzcore : z ∈ core
        · exact Set.mem_union_left _ hzcore
        · exfalso
          exact future_p_ne_query gen (Nat.lt_of_not_ge hst) hq hzcore hs

private theorem transcript_answer_step (gen : FeedbackGenerator) (t : ℕ) :
    (builtTranscript gen).answer t =
      Option.map (membershipAnswer (core ∪ Set.range (buildHistory gen (t + 1)).presentation))
        ((builtTranscript gen).query t) := by
  simp [builtTranscript, buildHistory, extendHistory]

private theorem built_follows_protocol (gen : FeedbackGenerator) :
    FollowsProtocol gen (builtTarget gen) (builtTranscript gen) := by
  intro t
  constructor
  · rw [transcript_q_step]
    congr 1
    · funext i
      exact history_p_eq gen (t + 1) i
    · funext i
      exact history_a_eq gen t i
  constructor
  · rw [transcript_answer_step]
    cases hq : (builtTranscript gen).query t with
    | none => simp
    | some z =>
        simp only [Option.map_some]
        have hiff := partial_mem_iff_final gen t z hq
        simp only [membershipAnswer]
        by_cases hp : z ∈ core ∪ Set.range (buildHistory gen (t + 1)).presentation <;>
          by_cases hf : z ∈ builtTarget gen <;> simp [hp, hf] at hiff ⊢
  · rw [transcript_y_step]
    congr 1
    · funext i
      exact history_p_eq gen (t + 1) i
    · funext i
      exact history_a_eq gen (t + 1) i

private theorem built_presented_by (gen : FeedbackGenerator) :
    PresentedBy builtPresenter (builtTranscript gen) := by
  intro t
  rw [transcript_p_step]
  simp only [builtPresenter]
  congr 1
  · funext i
    exact history_p_eq gen t i
  · funext i
    exact history_q_eq gen t i
  · funext i
    exact history_a_eq gen t i
  · funext i
    exact history_y_eq gen t i

end Stage3S2BProof

namespace Stage3S2BProof

open Stage3S2B

private theorem forbidden_card_le {t : ℕ} (p : Fin t → ℕ)
    (q : Fin t → Option ℕ) (y : Fin t → ℕ) :
    (forbidden p q y).card ≤ 3 * t := by
  classical
  have hp : (Finset.univ.image p).card ≤ t := by
    simpa using (Finset.card_image_le (s := (Finset.univ : Finset (Fin t))) (f := p))
  have hy : (Finset.univ.image y).card ≤ t := by
    simpa using (Finset.card_image_le (s := (Finset.univ : Finset (Fin t))) (f := y))
  have hq : (Finset.univ.biUnion fun i => (q i).toFinset).card ≤ t := by
    calc
      _ ≤ ∑ i ∈ (Finset.univ : Finset (Fin t)), ((q i).toFinset).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _i ∈ (Finset.univ : Finset (Fin t)), 1 := by
        apply Finset.sum_le_sum
        intro i hi
        cases q i <;> simp
      _ = t := by simp
  unfold forbidden
  have h₁ := Finset.card_union_le (Finset.univ.image p)
    (Finset.univ.biUnion fun i => (q i).toFinset)
  have h₂ := Finset.card_union_le
    ((Finset.univ.image p) ∪ (Finset.univ.biUnion fun i => (q i).toFinset))
    (Finset.univ.image y)
  omega

private theorem freshOrdinary_le (F : Finset ℕ) :
    freshOrdinary F ≤ 2 * F.card + 3 := by
  classical
  let candidates := (Finset.range (F.card + 1)).image code
  have hc : candidates.card = F.card + 1 := by
    simp [candidates, Finset.card_image_of_injective _ code_injective]
  obtain ⟨z, hzc, hzF⟩ := Finset.exists_mem_not_mem_of_card_lt_card
    (s := F) (t := candidates) (by omega : F.card < candidates.card)
  rcases Finset.mem_image.mp hzc with ⟨n, hn, rfl⟩
  have hnlt : n < F.card + 1 := Finset.mem_range.mp hn
  have hnle : n ≤ F.card := by omega
  have hfind : freshOrdinary F ≤ code n := by
    unfold freshOrdinary
    exact Nat.find_min' (exists_ordinary_not_mem F) ⟨code_not_core n, hzF⟩
  simp only [code] at hfind ⊢
  omega

private theorem presentation_odd_le (gen : FeedbackGenerator) (t : ℕ)
    (ht : t % 2 ≠ 0) : (builtTranscript gen).presentation t ≤ 6 * t + 3 := by
  rw [transcript_p_step]
  simp only [presenterStep, ht, if_false]
  calc
    freshOrdinary (forbidden (buildHistory gen t).presentation
      (buildHistory gen t).query (buildHistory gen t).output)
        ≤ 2 * (forbidden (buildHistory gen t).presentation
          (buildHistory gen t).query (buildHistory gen t).output).card + 3 :=
      freshOrdinary_le _
    _ ≤ 6 * t + 3 := by
      have h := forbidden_card_le (buildHistory gen t).presentation
        (buildHistory gen t).query (buildHistory gen t).output
      omega

private theorem scored_subset_core (gen : FeedbackGenerator) :
    scored (builtTarget gen) (builtTranscript gen).presentation
      (builtTranscript gen).output ⊆ core := by
  intro z hz
  rcases hz with ⟨hzK, t, hyt, hfresh⟩
  by_contra hzcore
  rcases hzK with hzcore' | ⟨s, hps⟩
  · exact hzcore hzcore'
  · have hst : t < s := by
      by_contra hnot
      apply hfresh
      exact ⟨s, Nat.le_of_not_gt hnot, hps⟩
    have hzord : (builtTranscript gen).output t ∈ ordinary := by
      rw [hyt]
      exact hzcore
    exact future_p_ne_output gen hst hzord (hps.trans hyt.symm)

end Stage3S2BProof

namespace Stage3S2BProof

open Stage3S2B

private theorem builtTarget_infinite (gen : FeedbackGenerator) :
    (builtTarget gen).Infinite := by
  apply (Set.infinite_range_of_injective (Nat.pow_right_injective (by omega : 2 ≤ 2))).mono
  intro z hz
  exact Set.mem_union_left _ hz

noncomputable def builtOrdered (gen : FeedbackGenerator) : OrderedLanguage where
  carrier := builtTarget gen
  enumeration := Nat.nth (fun z => z ∈ builtTarget gen)
  enumeration_injective := Nat.nth_injective (builtTarget_infinite gen)
  range_enumeration := Nat.range_nth_of_infinite (builtTarget_infinite gen)

private theorem builtOrdered_strictMono (gen : FeedbackGenerator) :
    InheritsAmbientOrder (builtOrdered gen) :=
  Nat.nth_strictMono (builtTarget_infinite gen)

private theorem nth_builtTarget_le (gen : FeedbackGenerator) (n : ℕ) :
    Nat.nth (fun z => z ∈ builtTarget gen) n ≤ 12 * n + 9 := by
  classical
  let samples : Finset ℕ :=
    (Finset.range (n + 1)).image fun r => (builtTranscript gen).presentation (2 * r + 1)
  have hs_card : samples.card = n + 1 := by
    rw [Finset.card_image_of_injective]
    · simp [samples]
    · intro a b hab
      have := presentation_injective gen hab
      omega
  have hs_sub : samples ⊆
      (Finset.range (12 * n + 10)).filter (fun z => z ∈ builtTarget gen) := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨r, hr, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_range]
    have hrn : r ≤ n := by
      have := Finset.mem_range.mp hr
      omega
    constructor
    · have hle := presentation_odd_le gen (2 * r + 1) (by omega)
      omega
    · exact Set.mem_union_right _ ⟨2 * r + 1, rfl⟩
  have hcount : n < Nat.count (fun z => z ∈ builtTarget gen) (12 * n + 10) := by
    rw [Nat.count_eq_card_filter_range]
    have := Finset.card_le_card hs_sub
    omega
  have := Nat.nth_lt_of_lt_count hcount
  omega

private theorem core_prefix_card (M : ℕ) (hM : M ≠ 0) :
    (by classical exact ((Finset.range (M + 1)).filter fun z => z ∈ core).card) =
      Nat.log 2 M + 1 := by
  classical
  let powers := (Finset.range (Nat.log 2 M + 1)).image fun k => 2 ^ k
  have heq : ((Finset.range (M + 1)).filter fun z => z ∈ core) = powers := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_range, powers, Finset.mem_image]
    constructor
    · rintro ⟨hzM, k, rfl⟩
      refine ⟨k, ?_, rfl⟩
      have hpow : 2 ^ k ≤ M := by
        change 2 ^ k < M + 1 at hzM
        omega
      have hk : k ≤ Nat.log 2 M := Nat.le_log_of_pow_le (by omega) hpow
      omega
    · rintro ⟨k, hk, rfl⟩
      have hklog : k ≤ Nat.log 2 M := by omega
      have hpM : 2 ^ k ≤ M := Nat.pow_le_of_le_log hM hklog
      constructor
      · change 2 ^ k < M + 1
        omega
      · exact ⟨k, rfl⟩
  rw [heq]
  dsimp [powers]
  rw [Finset.card_image_of_injective _ (Nat.pow_right_injective (by omega))]
  simp

private theorem ordered_core_prefix_le (gen : FeedbackGenerator) (n : ℕ) :
    (builtOrdered gen).prefixCount core n ≤ Nat.log 2 (12 * n + 9) + 1 := by
  classical
  let idx := (Finset.range n).filter fun i => (builtOrdered gen).enumeration i ∈ core
  let vals := idx.image (builtOrdered gen).enumeration
  have hcard : vals.card = (builtOrdered gen).prefixCount core n := by
    unfold GenLimit.KleinbergWei.OrderedLanguage.prefixCount
    dsimp [vals, idx]
    rw [Finset.card_image_of_injective _ (builtOrdered gen).enumeration_injective]
  have hsub : vals ⊆ (Finset.range (12 * n + 10)).filter (fun z => z ∈ core) := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨i, hi, rfl⟩
    have hi' := Finset.mem_filter.mp hi
    have hin : i < n := Finset.mem_range.mp hi'.1
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · have hi_le : (builtOrdered gen).enumeration i ≤
          (builtOrdered gen).enumeration n :=
        (builtOrdered_strictMono gen).monotone (Nat.le_of_lt hin)
      have hn := nth_builtTarget_le gen n
      change Nat.nth (fun z => z ∈ builtTarget gen) i ≤
        Nat.nth (fun z => z ∈ builtTarget gen) n at hi_le
      exact lt_of_le_of_lt hi_le (lt_of_le_of_lt hn (by omega))
    · exact hi'.2
  rw [← hcard, ← core_prefix_card (12 * n + 9) (by omega)]
  exact Finset.card_le_card hsub


private theorem logarithmic_bound_tendsto : Tendsto (fun n : ℕ =>
    (Real.logb 2 ((12 : ℝ) * n + 9) + 1) / (n : ℝ)) atTop (nhds 0) := by
  have hu : Tendsto (fun n : ℕ => (12 : ℝ) * n + 9) atTop atTop := by
    have hn : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop
    have h12 : Tendsto (fun n : ℕ => (12 : ℝ) * n) atTop atTop :=
      hn.const_mul_atTop (by norm_num)
    exact Filter.tendsto_atTop_add_const_right atTop (9 : ℝ) h12
  have hlogdivu : Tendsto (fun n : ℕ =>
      Real.log ((12 : ℝ) * n + 9) / ((12 : ℝ) * n + 9)) atTop (nhds 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hu
  have huratio : Tendsto (fun n : ℕ => ((12 : ℝ) * n + 9) / (n : ℝ))
      atTop (nhds 12) := by
    have h9 : Tendsto (fun n : ℕ => (9 : ℝ) * (1 / (n : ℝ))) atTop (nhds 0) := by
      convert (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => (9 : ℝ)) atTop (nhds 9)).mul
          tendsto_one_div_atTop_nhds_zero_nat using 1 <;> norm_num
    have h : Tendsto (fun n : ℕ => (12 : ℝ) + 9 * (1 / (n : ℝ)))
        atTop (nhds 12) := by
      convert (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => (12 : ℝ)) atTop (nhds 12)).add h9 using 1 <;>
          norm_num
    apply h.congr'
    filter_upwards [eventually_ne_atTop 0] with n hn
    field_simp
  have hlogdivn : Tendsto (fun n : ℕ =>
      Real.log ((12 : ℝ) * n + 9) / (n : ℝ)) atTop (nhds 0) := by
    have h := hlogdivu.mul huratio
    norm_num at h
    refine h.congr' ?_
    filter_upwards [eventually_ne_atTop 0] with n hn
    have hu0 : (12 : ℝ) * n + 9 ≠ 0 := by positivity
    field_simp
  have hlogb : Tendsto (fun n : ℕ =>
      Real.logb 2 ((12 : ℝ) * n + 9) / (n : ℝ)) atTop (nhds 0) := by
    have h := hlogdivn.div_const (Real.log 2)
    norm_num at h
    refine h.congr' ?_
    filter_upwards [eventually_ne_atTop 0] with n hn
    rw [Real.logb]
    field_simp
  have hone : Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ)) atTop (nhds 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have h := hlogb.add hone
  norm_num at h
  refine h.congr' ?_
  filter_upwards [eventually_ne_atTop 0] with n hn
  field_simp

private theorem scored_prefixCount_le_core (gen : FeedbackGenerator) (n : ℕ) :
    (builtOrdered gen).prefixCount
        (scored (builtTarget gen) (builtTranscript gen).presentation
          (builtTranscript gen).output) n ≤
      (builtOrdered gen).prefixCount core n := by
  classical
  unfold GenLimit.KleinbergWei.OrderedLanguage.prefixCount
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter] at hi ⊢
  exact ⟨hi.1, scored_subset_core gen hi.2⟩

private theorem scored_prefixRatio_tendsto (gen : FeedbackGenerator) :
    Tendsto ((builtOrdered gen).prefixRatio
      (scored (builtTarget gen) (builtTranscript gen).presentation
        (builtTranscript gen).output)) atTop (nhds 0) := by
  apply squeeze_zero'
  · exact Eventually.of_forall fun n => by
      unfold GenLimit.KleinbergWei.OrderedLanguage.prefixRatio
      split_ifs
      · exact le_rfl
      · positivity
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : n ≠ 0 := by omega
    unfold GenLimit.KleinbergWei.OrderedLanguage.prefixRatio
    simp only [hn0, if_false]
    have hscore := scored_prefixCount_le_core gen n
    have hcore := ordered_core_prefix_le gen n
    have hcount : (builtOrdered gen).prefixCount
          (scored (builtTarget gen) (builtTranscript gen).presentation
            (builtTranscript gen).output) n ≤ Nat.log 2 (12 * n + 9) + 1 :=
      hscore.trans hcore
    have hcountR : ((builtOrdered gen).prefixCount
          (scored (builtTarget gen) (builtTranscript gen).presentation
            (builtTranscript gen).output) n : ℝ) ≤
        (Nat.log 2 (12 * n + 9) + 1 : ℕ) := by
      exact_mod_cast hcount
    have hlog := Real.natLog_le_logb (12 * n + 9) 2
    have hnum : ((builtOrdered gen).prefixCount
          (scored (builtTarget gen) (builtTranscript gen).presentation
            (builtTranscript gen).output) n : ℝ) ≤
        Real.logb 2 ((12 : ℝ) * n + 9) + 1 := by
      norm_num [Nat.cast_add] at hcountR
      norm_num [Nat.cast_add, Nat.cast_mul] at hlog ⊢
      linarith
    exact div_le_div_of_nonneg_right hnum (by positivity)
  · exact logarithmic_bound_tendsto

private theorem built_scored_density_zero (gen : FeedbackGenerator) :
    (builtOrdered gen).upperDensity
      (scored (builtTarget gen) (builtTranscript gen).presentation
        (builtTranscript gen).output) = 0 := by
  exact (scored_prefixRatio_tendsto gen).limsup_eq

end Stage3S2BProof

namespace Stage3S2BProof

open Stage3S2B

theorem negative_claim : NegativeClaim := by
  intro gen _hgen
  refine ⟨builtTarget gen, builtTarget_mem_class gen, builtPresenter,
    builtTranscript gen, builtOrdered gen, ?_⟩
  exact ⟨rfl, builtOrdered_strictMono gen, built_presented_by gen,
    built_follows_protocol gen, built_clean gen, presentation_injective gen,
    built_complete gen, built_scored_density_zero gen⟩

end Stage3S2BProof
