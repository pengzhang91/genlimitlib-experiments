import Stage3Model
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

open Set Filter
open scoped Topology

namespace Stage3Proof

open Stage3S2B

lemma pow_two_injective : Function.Injective (fun k : ℕ => 2 ^ k) := by
  intro a b h
  exact Nat.pow_right_injective (by omega) h

lemma core_infinite : core.Infinite := by
  exact Set.infinite_range_of_injective pow_two_injective

lemma three_odd_not_core (n : ℕ) : 2 * n + 3 ∈ ordinary := by
  intro h
  rcases h with ⟨k, hk⟩
  have hk0 : k ≠ 0 := by
    intro hzero
    subst k
    norm_num at hk
  have hdvd : 2 ∣ 2 * n + 3 := by
    rw [← hk]
    exact dvd_pow_self 2 hk0
  omega

lemma odd_range_injective : Function.Injective (fun n : ℕ => 2 * n + 3) := by
  intro a b h
  dsimp at h
  omega

lemma ordinary_infinite : ordinary.Infinite := by
  apply (Set.infinite_range_of_injective odd_range_injective).mono
  rintro z ⟨n, rfl⟩
  exact three_odd_not_core n

lemma targetClass_not_countable : ¬ targetClass.Countable := by
  intro hc
  have hne : targetClass.Nonempty := by
    refine ⟨core, ?_⟩
    exact ⟨∅, empty_subset _, by simp⟩
  obtain ⟨f, hf⟩ := hc.exists_eq_range hne
  let A : Language := {z | ∃ n, z = 2 * n + 3 ∧ z ∉ f n}
  let K : Language := core ∪ A
  have hK : K ∈ targetClass := by
    refine ⟨A, ?_, rfl⟩
    intro z hz
    rcases hz with ⟨n, rfl, _⟩
    exact three_odd_not_core n
  have Krange : K ∈ Set.range f := hf ▸ hK
  rcases Krange with ⟨n, hn⟩
  have hord := three_odd_not_core n
  have hdiag : (2 * n + 3 ∈ K) ↔ (2 * n + 3 ∉ f n) := by
    simp only [K, A, mem_union, mem_setOf_eq]
    constructor
    · intro h
      rcases h with hc' | hA
      · exact False.elim (hord hc')
      · rcases hA with ⟨m, hm, hnot⟩
        have : m = n := by omega
        simpa [this] using hnot
    · intro hnot
      exact Or.inr ⟨n, rfl, hnot⟩
  rw [hn] at hdiag
  exact iff_not_self hdiag

lemma uniform_generation : UniformlyGeneratableWithoutSamples := by
  refine ⟨fun k => 2 ^ k, pow_two_injective, 0, ?_⟩
  intro K hK t _
  rcases hK with ⟨A, hA, rfl⟩
  exact Or.inl ⟨t, rfl⟩

structure Round where
  presentation : ℕ
  query : Option ℕ
  answer : Option Bool
  output : ℕ

abbrev History (t : ℕ) := Fin t → Round

def forbiddenFinset {t : ℕ} (h : History t) : Finset ℕ :=
  (Finset.univ : Finset (Fin t)).biUnion fun i =>
    {h i |>.presentation, h i |>.output} ∪
      match (h i).query with | none => ∅ | some z => {z}

def forbidden {t : ℕ} (h : History t) : Set ℕ := forbiddenFinset h

noncomputable def chooseOrdinary {t : ℕ} (h : History t) : ℕ := by
  classical
  exact Nat.find (ordinary_infinite.exists_notMem_finset (forbiddenFinset h))

lemma chooseOrdinary_spec {t : ℕ} (h : History t) :
    chooseOrdinary h ∈ ordinary ∧ chooseOrdinary h ∉ forbidden h := by
  classical
  exact Nat.find_spec (ordinary_infinite.exists_notMem_finset (forbiddenFinset h))

lemma forbiddenFinset_card_le {t : ℕ} (h : History t) :
    (forbiddenFinset h).card ≤ 3 * t := by
  classical
  let F : Fin t → Finset ℕ := fun i =>
    {h i |>.presentation, h i |>.output} ∪
      match (h i).query with | none => ∅ | some z => {z}
  change ((Finset.univ : Finset (Fin t)).biUnion F).card ≤ 3 * t
  calc
    ((Finset.univ : Finset (Fin t)).biUnion F).card
        ≤ ∑ i : Fin t, (F i).card := Finset.card_biUnion_le
    _ ≤ ∑ _i : Fin t, 3 := by
      apply Finset.sum_le_sum
      intro i _
      cases hq : (h i).query with
      | none =>
          simpa [F, hq] using (Finset.card_le_two (a := (h i).presentation) (b := (h i).output)).trans (by omega)
      | some z =>
          simpa [F, hq] using (Finset.card_le_three (a := (h i).presentation)
            (b := (h i).output) (c := z))
    _ = 3 * t := by simp [mul_comm]

lemma chooseOrdinary_le {t : ℕ} (h : History t) : chooseOrdinary h ≤ 6 * t + 3 := by
  classical
  let candidates := (Finset.range (3 * t + 1)).image (fun n => 2 * n + 3)
  have hcand : candidates.card = 3 * t + 1 := by
    simp [candidates, Finset.card_image_of_injective, odd_range_injective]
  have hf := forbiddenFinset_card_le h
  have hcard : (forbiddenFinset h).card < candidates.card := by
    rw [hcand]
    omega
  obtain ⟨z, hzcan, hzforbid⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  rcases Finset.mem_image.mp hzcan with ⟨n, hn, rfl⟩
  have hfind : chooseOrdinary h ≤ 2 * n + 3 := by
    exact Nat.find_le ⟨three_odd_not_core n, hzforbid⟩
  have hnlt : n < 3 * t + 1 := Finset.mem_range.mp hn
  omega

noncomputable def choosePresentation {t : ℕ} (h : History t) : ℕ := by
  classical
  exact if t ∈ core then t else chooseOrdinary h

def currentLanguage {t : ℕ} (h : History t) (x : ℕ) : Language :=
  core ∪ {z | z = x ∨ ∃ i, (h i).presentation = z}

noncomputable def makeRound (gen : FeedbackGenerator) {t : ℕ} (h : History t) : Round := by
  let x := choosePresentation h
  let q := gen.query t
    (fun i => if hi : i.1 < t then (h ⟨i, hi⟩).presentation else x)
    (fun i => (h i).answer)
  let a := match q with
    | none => none
    | some z => some (membershipAnswer (currentLanguage h x) z)
  let y := gen.output t
    (fun i => if hi : i.1 < t then (h ⟨i, hi⟩).presentation else x)
    (fun i => if hi : i.1 < t then (h ⟨i, hi⟩).answer else a)
  exact ⟨x, q, a, y⟩

noncomputable def history (gen : FeedbackGenerator) : (t : ℕ) → History t
  | 0 => fun i => Fin.elim0 i
  | t + 1 => fun i =>
      if hi : i.1 < t then history gen t ⟨i, hi⟩ else makeRound gen (history gen t)

noncomputable def roundAt (gen : FeedbackGenerator) (t : ℕ) : Round :=
  makeRound gen (history gen t)

noncomputable def adversarialTranscript (gen : FeedbackGenerator) : Transcript where
  presentation := fun t => (roundAt gen t).presentation
  query := fun t => (roundAt gen t).query
  answer := fun t => (roundAt gen t).answer
  output := fun t => (roundAt gen t).output

noncomputable def adversarialPresenter : CausalPresenter where
  next := fun t px pq pa py => by
    let h : History t := fun i => ⟨px i, pq i, pa i, py i⟩
    exact choosePresentation h

lemma history_get (gen : FeedbackGenerator) {i n : ℕ} (hi : i < n) :
    history gen n ⟨i, hi⟩ = roundAt gen i := by
  induction n with
  | zero => omega
  | succ n ih =>
      simp only [history]
      split <;> rename_i hlt
      · exact ih hlt
      · have : i = n := by omega
        subst i
        rfl

lemma makeRound_presentation (gen : FeedbackGenerator) (t : ℕ) :
    (roundAt gen t).presentation = choosePresentation (history gen t) := by
  rfl

lemma presentation_eq_choose (gen : FeedbackGenerator) (t : ℕ) :
    (adversarialTranscript gen).presentation t = choosePresentation (history gen t) := by
  rfl

lemma history_forbidden_presentation (gen : FeedbackGenerator) {s t : ℕ} (hst : s < t) :
    (adversarialTranscript gen).presentation s ∈ forbidden (history gen t) := by
  simp only [forbidden, forbiddenFinset, Finset.mem_coe, Finset.mem_biUnion,
    Finset.mem_univ, true_and]
  refine ⟨⟨s, hst⟩, ?_⟩
  rw [history_get gen hst]
  simp [adversarialTranscript]

lemma history_forbidden_query (gen : FeedbackGenerator) {s t z : ℕ} (hst : s < t)
    (hq : (adversarialTranscript gen).query s = some z) :
    z ∈ forbidden (history gen t) := by
  simp only [forbidden, forbiddenFinset, Finset.mem_coe, Finset.mem_biUnion,
    Finset.mem_univ, true_and]
  refine ⟨⟨s, hst⟩, ?_⟩
  rw [history_get gen hst]
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
  right
  simp only [adversarialTranscript] at hq
  simp [hq]

lemma history_forbidden_output (gen : FeedbackGenerator) {s t : ℕ} (hst : s < t) :
    (adversarialTranscript gen).output s ∈ forbidden (history gen t) := by
  simp only [forbidden, forbiddenFinset, Finset.mem_coe, Finset.mem_biUnion,
    Finset.mem_univ, true_and]
  refine ⟨⟨s, hst⟩, ?_⟩
  rw [history_get gen hst]
  simp [adversarialTranscript]

lemma presentation_core_iff (gen : FeedbackGenerator) (t : ℕ) (ht : t ∈ core) :
    (adversarialTranscript gen).presentation t = t := by
  rw [presentation_eq_choose]
  simp [choosePresentation, ht]

lemma presentation_ordinary_of_not_core (gen : FeedbackGenerator) (t : ℕ) (ht : t ∉ core) :
    (adversarialTranscript gen).presentation t ∈ ordinary := by
  rw [presentation_eq_choose]
  simpa [choosePresentation, ht] using (chooseOrdinary_spec (history gen t)).1

lemma presentation_fresh_of_not_core (gen : FeedbackGenerator) (t : ℕ) (ht : t ∉ core) :
    (adversarialTranscript gen).presentation t ∉ forbidden (history gen t) := by
  rw [presentation_eq_choose]
  simpa [choosePresentation, ht] using (chooseOrdinary_spec (history gen t)).2

lemma presentation_ne_of_lt (gen : FeedbackGenerator) {s t : ℕ} (hst : s < t) :
    (adversarialTranscript gen).presentation s ≠
      (adversarialTranscript gen).presentation t := by
  intro heq
  by_cases ht : t ∈ core
  · have hxt := presentation_core_iff gen t ht
    by_cases hs : s ∈ core
    · have hxs := presentation_core_iff gen s hs
      rw [hxs, hxt] at heq
      omega
    · have hsordinary := presentation_ordinary_of_not_core gen s hs
      rw [heq, hxt] at hsordinary
      exact hsordinary ht
  · exact presentation_fresh_of_not_core gen t ht
      (heq ▸ history_forbidden_presentation gen hst)

lemma presentation_injective (gen : FeedbackGenerator) :
    Function.Injective (adversarialTranscript gen).presentation := by
  intro s t heq
  rcases lt_trichotomy s t with hst | hst | hst
  · exact False.elim (presentation_ne_of_lt gen hst heq)
  · exact hst
  · exact False.elim (presentation_ne_of_lt gen hst heq.symm)

lemma core_subset_presentation_range (gen : FeedbackGenerator) :
    core ⊆ Set.range (adversarialTranscript gen).presentation := by
  intro z hz
  exact ⟨z, presentation_core_iff gen z hz⟩

noncomputable def adversarialTarget (gen : FeedbackGenerator) : Language :=
  Set.range (adversarialTranscript gen).presentation

lemma adversarialTarget_mem_class (gen : FeedbackGenerator) :
    adversarialTarget gen ∈ targetClass := by
  let A : Language := adversarialTarget gen ∩ ordinary
  refine ⟨A, inter_subset_right, ?_⟩
  ext z
  constructor
  · intro hz
    change z ∈ core ∨ z ∈ A
    by_cases hc : z ∈ core
    · exact Or.inl hc
    · exact Or.inr ⟨hz, hc⟩
  · intro hz
    change z ∈ core ∨ z ∈ A at hz
    rcases hz with hc | hA
    · exact core_subset_presentation_range gen hc
    · exact hA.1

lemma adversarial_clean (gen : FeedbackGenerator) :
    Clean (adversarialTranscript gen).presentation (adversarialTarget gen) := by
  intro t
  exact ⟨t, rfl⟩

lemma adversarial_complete (gen : FeedbackGenerator) :
    Complete (adversarialTranscript gen).presentation (adversarialTarget gen) := by
  intro z hz
  exact hz

lemma adversarial_presented (gen : FeedbackGenerator) :
    PresentedBy adversarialPresenter (adversarialTranscript gen) := by
  intro t
  rw [presentation_eq_choose]
  congr 1
  funext i
  rw [history_get gen i.isLt]
  rfl


lemma query_eq_makeRound (gen : FeedbackGenerator) (t : ℕ) :
    (adversarialTranscript gen).query t = gen.query t
      (fun i => (adversarialTranscript gen).presentation i)
      (fun i => (adversarialTranscript gen).answer i) := by
  change (roundAt gen t).query = _
  rw [show (roundAt gen t).query = gen.query t
      (fun i => if hi : i.1 < t then (history gen t ⟨i, hi⟩).presentation
        else (roundAt gen t).presentation)
      (fun i => (history gen t i).answer) by rfl]
  congr 1
  · funext i
    split <;> rename_i hi
    · rw [history_get gen hi]
      rfl
    · have hit : i.1 = t := by omega
      simpa [hit, adversarialTranscript]
  · funext i
    rw [history_get gen i.isLt]
    rfl

lemma output_eq_makeRound (gen : FeedbackGenerator) (t : ℕ) :
    (adversarialTranscript gen).output t = gen.output t
      (fun i => (adversarialTranscript gen).presentation i)
      (fun i => (adversarialTranscript gen).answer i) := by
  change (roundAt gen t).output = _
  rw [show (roundAt gen t).output = gen.output t
      (fun i => if hi : i.1 < t then (history gen t ⟨i, hi⟩).presentation
        else (roundAt gen t).presentation)
      (fun i => if hi : i.1 < t then (history gen t ⟨i, hi⟩).answer
        else (roundAt gen t).answer) by rfl]
  congr 1
  · funext i
    split <;> rename_i hi
    · rw [history_get gen hi]
      rfl
    · have hit : i.1 = t := by omega
      simpa [hit, adversarialTranscript]
  · funext i
    split <;> rename_i hi
    · rw [history_get gen hi]
      rfl
    · have hit : i.1 = t := by omega
      simpa [hit, adversarialTranscript]

lemma queried_mem_target_iff_current (gen : FeedbackGenerator) {t z : ℕ}
    (hq : (adversarialTranscript gen).query t = some z) :
    z ∈ adversarialTarget gen ↔
      z ∈ currentLanguage (history gen t) ((adversarialTranscript gen).presentation t) := by
  constructor
  · rintro ⟨s, hs⟩
    by_cases hc : z ∈ core
    · exact Or.inl hc
    · right
      by_cases hst : s < t
      · right
        exact ⟨⟨s, hst⟩, by rw [history_get gen hst]; exact hs⟩
      · by_cases hts : t < s
        · have hsnoncore : s ∉ core := by
            intro hsc
            rw [presentation_core_iff gen s hsc] at hs
            exact hc (hs ▸ hsc)
          have hfresh := presentation_fresh_of_not_core gen s hsnoncore
          exfalso
          apply hfresh
          have hz := history_forbidden_query gen hts hq
          exact hs ▸ hz
        · have : s = t := by omega
          subst s
          exact Or.inl hs.symm
  · intro hz
    rcases hz with hc | hz
    · exact core_subset_presentation_range gen hc
    · rcases hz with rfl | ⟨i, hi⟩
      · exact ⟨t, rfl⟩
      · rw [history_get gen i.isLt] at hi
        exact ⟨i, hi⟩

lemma answer_eq_target (gen : FeedbackGenerator) (t : ℕ) :
    (adversarialTranscript gen).answer t =
      match (adversarialTranscript gen).query t with
      | none => none
      | some z => some (membershipAnswer (adversarialTarget gen) z) := by
  change (roundAt gen t).answer =
    match (roundAt gen t).query with
    | none => none
    | some z => some (membershipAnswer (adversarialTarget gen) z)
  rw [show (roundAt gen t).answer =
      match (roundAt gen t).query with
      | none => none
      | some z => some (membershipAnswer
          (currentLanguage (history gen t) (roundAt gen t).presentation) z) by rfl]
  cases hq : (roundAt gen t).query with
  | none => rfl
  | some z =>
      simp only
      congr 1
      unfold membershipAnswer
      classical
      exact decide_eq_decide.mpr (queried_mem_target_iff_current gen hq).symm

lemma adversarial_protocol (gen : FeedbackGenerator) :
    FollowsProtocol gen (adversarialTarget gen) (adversarialTranscript gen) := by
  intro t
  exact ⟨query_eq_makeRound gen t, answer_eq_target gen t, output_eq_makeRound gen t⟩


lemma eventual_output_mem_core (gen : FeedbackGenerator) (T : ℕ)
    (hfuture : ∀ t, T ≤ t →
      (adversarialTranscript gen).output t ∈ adversarialTarget gen ∧
      (adversarialTranscript gen).output t ∉
        observedThrough (adversarialTranscript gen).presentation t)
    {t : ℕ} (ht : T ≤ t) :
    (adversarialTranscript gen).output t ∈ core := by
  by_contra hcore
  obtain ⟨s, hs⟩ := (hfuture t ht).1
  have hts : t < s := by
    by_contra hnot
    apply (hfuture t ht).2
    exact ⟨s, by omega, hs⟩
  have hsnoncore : s ∉ core := by
    intro hsc
    have hx := presentation_core_iff gen s hsc
    apply hcore
    rw [← hs, hx]
    exact hsc
  apply presentation_fresh_of_not_core gen s hsnoncore
  have hout := history_forbidden_output gen hts
  exact hs.symm ▸ hout

noncomputable def earlyOutputs (gen : FeedbackGenerator) (T : ℕ) : Language :=
  Set.range (fun i : Fin T => (adversarialTranscript gen).output i)

lemma earlyOutputs_finite (gen : FeedbackGenerator) (T : ℕ) :
    (earlyOutputs gen T).Finite := by
  exact Set.finite_range _

lemma scored_subset_core_union_early (gen : FeedbackGenerator) (T : ℕ)
    (hfuture : ∀ t, T ≤ t →
      (adversarialTranscript gen).output t ∈ adversarialTarget gen ∧
      (adversarialTranscript gen).output t ∉
        observedThrough (adversarialTranscript gen).presentation t) :
    scored (adversarialTarget gen) (adversarialTranscript gen).presentation
        (adversarialTranscript gen).output ⊆ core ∪ earlyOutputs gen T := by
  intro z hz
  rcases hz.2 with ⟨t, hyt, _⟩
  by_cases ht : T ≤ t
  · left
    rw [← hyt]
    exact eventual_output_mem_core gen T hfuture ht
  · right
    exact ⟨⟨t, by omega⟩, hyt⟩

lemma adversarialTarget_infinite (gen : FeedbackGenerator) :
    (adversarialTarget gen).Infinite :=
  core_infinite.mono (core_subset_presentation_range gen)

noncomputable def orderedAdversarialTarget (gen : FeedbackGenerator) : OrderedLanguage where
  carrier := adversarialTarget gen
  enumeration := Nat.nth (fun z => z ∈ adversarialTarget gen)
  enumeration_injective := Nat.nth_injective (adversarialTarget_infinite gen)
  range_enumeration := Nat.range_nth_of_infinite (adversarialTarget_infinite gen)

lemma orderedAdversarialTarget_strictMono (gen : FeedbackGenerator) :
    InheritsAmbientOrder (orderedAdversarialTarget gen) := by
  exact Nat.nth_strictMono (adversarialTarget_infinite gen)

lemma presentation_le (gen : FeedbackGenerator) (t : ℕ) :
    (adversarialTranscript gen).presentation t ≤ 6 * t + 3 := by
  by_cases ht : t ∈ core
  · rw [presentation_core_iff gen t ht]
    omega
  · rw [presentation_eq_choose]
    simpa [choosePresentation, ht] using chooseOrdinary_le (history gen t)

lemma ordered_enumeration_le (gen : FeedbackGenerator) (n : ℕ) :
    (orderedAdversarialTarget gen).enumeration n ≤ 6 * n + 3 := by
  classical
  let values := (Finset.range (n + 1)).image (adversarialTranscript gen).presentation
  have hcard : values.card = n + 1 := by
    simp [values, Finset.card_image_of_injective, presentation_injective gen]
  have hsub : values ⊆ (Finset.range (6 * n + 4)).filter
      (fun z => z ∈ adversarialTarget gen) := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨t, ht, rfl⟩
    have htn : t ≤ n := by
      have := Finset.mem_range.mp ht
      omega
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · have := presentation_le gen t
      omega
    · exact ⟨t, rfl⟩
  have hcount : n < Nat.count (fun z => z ∈ adversarialTarget gen) (6 * n + 4) := by
    rw [Nat.count_eq_card_filter_range]
    have := Finset.card_le_card hsub
    rw [hcard] at this
    omega
  exact Nat.lt_succ_iff.mp (Nat.nth_lt_of_lt_count hcount)

lemma core_count_le_log (m : ℕ) :
    @Nat.count (fun z => z ∈ core) (Classical.decPred _) m ≤ Nat.log 2 m + 1 := by
  classical
  rw [Nat.count_eq_card_filter_range]
  let powers := (Finset.range (Nat.log 2 m + 1)).image (fun k : ℕ => 2 ^ k)
  calc
    ((Finset.range m).filter fun z => z ∈ core).card ≤ powers.card := by
      apply Finset.card_le_card
      intro z hz
      simp only [Finset.mem_filter, Finset.mem_range] at hz
      rcases hz.2 with ⟨k, rfl⟩
      apply Finset.mem_image.mpr
      refine ⟨k, Finset.mem_range.mpr ?_, rfl⟩
      have hpow : 2 ^ k ≤ m := Nat.le_of_lt hz.1
      have := Nat.le_log_of_pow_le (by omega : 1 < 2) hpow
      omega
    _ = Nat.log 2 m + 1 := by
      simp [powers, Finset.card_image_of_injective, pow_two_injective]


lemma prefixCount_mono (K : OrderedLanguage) {A B : Language} (hAB : A ⊆ B) (n : ℕ) :
    K.prefixCount A n ≤ K.prefixCount B n := by
  classical
  unfold GenLimit.KleinbergWei.OrderedLanguage.prefixCount
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter] at hi ⊢
  exact ⟨hi.1, hAB hi.2⟩

lemma prefixCount_core_le_log (gen : FeedbackGenerator) (n : ℕ) :
    (orderedAdversarialTarget gen).prefixCount core n ≤ Nat.log 2 (6 * n + 4) + 1 := by
  classical
  let indices := (Finset.range n).filter fun i =>
    (orderedAdversarialTarget gen).enumeration i ∈ core
  let values := indices.image (orderedAdversarialTarget gen).enumeration
  have hcard : values.card = indices.card := by
    exact Finset.card_image_of_injective _
      (orderedAdversarialTarget gen).enumeration_injective
  have hsub : values ⊆ (Finset.range (6 * n + 4)).filter (fun z => z ∈ core) := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨i, hi, rfl⟩
    have hin : i < n := (Finset.mem_filter.mp hi).1 |> Finset.mem_range.mp
    have hbound := ordered_enumeration_le gen i
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, (Finset.mem_filter.mp hi).2⟩
  change indices.card ≤ _
  rw [← hcard]
  calc
    values.card ≤ ((Finset.range (6 * n + 4)).filter (fun z => z ∈ core)).card :=
      Finset.card_le_card hsub
    _ = @Nat.count (fun z => z ∈ core) (Classical.decPred _) (6 * n + 4) := by
      rw [Nat.count_eq_card_filter_range]
    _ ≤ _ := core_count_le_log _

lemma prefixCount_finite_le (K : OrderedLanguage) (F : Language) (hF : F.Finite) (n : ℕ) :
    K.prefixCount F n ≤ hF.toFinset.card := by
  classical
  let indices := (Finset.range n).filter fun i => K.enumeration i ∈ F
  let values := indices.image K.enumeration
  have hcard : values.card = indices.card := by
    exact Finset.card_image_of_injective _ K.enumeration_injective
  change indices.card ≤ hF.toFinset.card
  rw [← hcard]
  apply Finset.card_le_card
  intro z hz
  rcases Finset.mem_image.mp hz with ⟨i, hi, rfl⟩
  exact (Set.Finite.mem_toFinset hF).2 ((Finset.mem_filter.mp hi).2)

lemma prefixCount_core_union_finite_le (gen : FeedbackGenerator)
    (F : Language) (hF : F.Finite) (n : ℕ) :
    (orderedAdversarialTarget gen).prefixCount (core ∪ F) n ≤
      Nat.log 2 (6 * n + 4) + 1 + hF.toFinset.card := by
  classical
  unfold GenLimit.KleinbergWei.OrderedLanguage.prefixCount
  let coreIndices := (Finset.range n).filter fun i =>
    (orderedAdversarialTarget gen).enumeration i ∈ core
  let finiteIndices := (Finset.range n).filter fun i =>
    (orderedAdversarialTarget gen).enumeration i ∈ F
  refine (Finset.card_le_card (t := coreIndices ∪ finiteIndices) ?_).trans ?_
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_range, mem_union] at hi
    simp only [Finset.mem_union, coreIndices, finiteIndices, Finset.mem_filter,
      Finset.mem_range]
    rcases hi.2 with hc | hF'
    · exact Or.inl ⟨hi.1, hc⟩
    · exact Or.inr ⟨hi.1, hF'⟩
  refine (Finset.card_union_le coreIndices finiteIndices).trans ?_
  apply Nat.add_le_add
  · let values := coreIndices.image (orderedAdversarialTarget gen).enumeration
    have hcard : values.card = coreIndices.card := by
      exact Finset.card_image_of_injective _
        (orderedAdversarialTarget gen).enumeration_injective
    rw [← hcard]
    calc
      values.card ≤ ((Finset.range (6 * n + 4)).filter (fun z => z ∈ core)).card := by
        apply Finset.card_le_card
        intro z hz
        rcases Finset.mem_image.mp hz with ⟨i, hi, rfl⟩
        have hin : i < n := by
          exact Finset.mem_range.mp (Finset.mem_filter.mp hi).1
        have hbound := ordered_enumeration_le gen i
        simp only [Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, (Finset.mem_filter.mp hi).2⟩
      _ = @Nat.count (fun z => z ∈ core) (Classical.decPred _) (6 * n + 4) := by
        rw [Nat.count_eq_card_filter_range]
      _ ≤ _ := core_count_le_log _
  · let values := finiteIndices.image (orderedAdversarialTarget gen).enumeration
    have hcard : values.card = finiteIndices.card := by
      exact Finset.card_image_of_injective _
        (orderedAdversarialTarget gen).enumeration_injective
    rw [← hcard]
    apply Finset.card_le_card
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨i, hi, rfl⟩
    exact (Set.Finite.mem_toFinset hF).2 (Finset.mem_filter.mp hi).2


lemma scored_prefixCount_le (gen : FeedbackGenerator) (T : ℕ)
    (hfuture : ∀ t, T ≤ t →
      (adversarialTranscript gen).output t ∈ adversarialTarget gen ∧
      (adversarialTranscript gen).output t ∉
        observedThrough (adversarialTranscript gen).presentation t)
    (n : ℕ) :
    (orderedAdversarialTarget gen).prefixCount
        (scored (adversarialTarget gen) (adversarialTranscript gen).presentation
          (adversarialTranscript gen).output) n ≤
      Nat.log 2 (6 * n + 4) + 1 + (earlyOutputs_finite gen T).toFinset.card := by
  calc
    _ ≤ (orderedAdversarialTarget gen).prefixCount (core ∪ earlyOutputs gen T) n :=
      prefixCount_mono _ (scored_subset_core_union_early gen T hfuture) n
    _ ≤ (Nat.log 2 (6 * n + 4) + 1) +
        (earlyOutputs_finite gen T).toFinset.card :=
      prefixCount_core_union_finite_le gen _ (earlyOutputs_finite gen T) n


lemma log_ratio_tendsto_zero (c : ℕ) :
    Tendsto (fun n : ℕ =>
      ((Nat.log 2 (6 * n + 4) + c : ℕ) : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
    simpa [Function.comp_def, id] using
      Real.isLittleO_log_id_atTop.natCast_atTop.tendsto_div_nhds_zero
  have hlogtwo : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  let C : ℝ := Real.log 10 / Real.log 2 + c
  let upper : ℕ → ℝ := fun n =>
    C / (n : ℝ) + (1 / Real.log 2) * (Real.log (n : ℝ) / (n : ℝ))
  have hupper : Tendsto upper atTop (𝓝 0) := by
    have hconst : Tendsto (fun n : ℕ => C / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    have hscaled := hlog.const_mul (1 / Real.log 2)
    simpa [upper] using hconst.add hscaled
  apply squeeze_zero' (g := upper)
  · exact Eventually.of_forall fun n => by positivity
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    have haffine : Real.log (((6 * n + 4 : ℕ) : ℝ)) ≤
        Real.log 10 + Real.log (n : ℝ) := by
      rw [← Real.log_mul (by norm_num : (10 : ℝ) ≠ 0)
        (by exact_mod_cast (Nat.ne_of_gt (show 0 < n by omega)))]
      apply Real.log_le_log
      · positivity
      · norm_num at *
        exact_mod_cast (show 6 * n + 4 ≤ 10 * n by omega)
    have hnat : (Nat.log 2 (6 * n + 4) : ℝ) ≤
        Real.logb (2 : ℝ) (((6 * n + 4 : ℕ) : ℝ)) :=
      Real.natLog_le_logb (6 * n + 4) 2
    have hnumer : ((Nat.log 2 (6 * n + 4) + c : ℕ) : ℝ) ≤
        (Real.log 10 + Real.log (n : ℝ)) / Real.log 2 + c := by
      calc
        ((Nat.log 2 (6 * n + 4) + c : ℕ) : ℝ) =
            (Nat.log 2 (6 * n + 4) : ℝ) + c := by norm_num
        _ ≤ Real.logb (2 : ℝ) (((6 * n + 4 : ℕ) : ℝ)) + c :=
          add_le_add_right hnat _
        _ = Real.log (((6 * n + 4 : ℕ) : ℝ)) / Real.log 2 + c := by
          simp [Real.logb]
        _ ≤ (Real.log 10 + Real.log (n : ℝ)) / Real.log 2 + c := by
          gcongr
    apply (div_le_iff₀ hnpos).2
    calc
      ((Nat.log 2 (6 * n + 4) + c : ℕ) : ℝ) ≤
          (Real.log 10 + Real.log (n : ℝ)) / Real.log 2 + c := hnumer
      _ = upper n * (n : ℝ) := by
        dsimp [upper, C]
        field_simp
        ring
  · exact hupper


lemma scored_prefixRatio_tendsto_zero (gen : FeedbackGenerator) (T : ℕ)
    (hfuture : ∀ t, T ≤ t →
      (adversarialTranscript gen).output t ∈ adversarialTarget gen ∧
      (adversarialTranscript gen).output t ∉
        observedThrough (adversarialTranscript gen).presentation t) :
    Tendsto ((orderedAdversarialTarget gen).prefixRatio
      (scored (adversarialTarget gen) (adversarialTranscript gen).presentation
        (adversarialTranscript gen).output)) atTop (𝓝 0) := by
  let finiteCard := (earlyOutputs_finite gen T).toFinset.card
  let upper : ℕ → ℝ := fun n =>
    ((Nat.log 2 (6 * n + 4) + (1 + finiteCard) : ℕ) : ℝ) / (n : ℝ)
  have hupper : Tendsto upper atTop (𝓝 0) := by
    exact log_ratio_tendsto_zero (1 + finiteCard)
  apply squeeze_zero' (g := upper)
  · exact Eventually.of_forall fun n => by
      unfold GenLimit.KleinbergWei.OrderedLanguage.prefixRatio
      split
      · simp
      · positivity
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hnzero : n ≠ 0 := by omega
    unfold GenLimit.KleinbergWei.OrderedLanguage.prefixRatio
    rw [if_neg hnzero]
    apply div_le_div_of_nonneg_right _ (by positivity)
    have hcount := scored_prefixCount_le gen T hfuture n
    have hcount' :
        (orderedAdversarialTarget gen).prefixCount
          (scored (adversarialTarget gen) (adversarialTranscript gen).presentation
            (adversarialTranscript gen).output) n ≤
          Nat.log 2 (6 * n + 4) + (1 + finiteCard) := by
      dsimp [finiteCard]
      omega
    exact_mod_cast hcount'
  · exact hupper

lemma scored_upperDensity_zero (gen : FeedbackGenerator) (T : ℕ)
    (hfuture : ∀ t, T ≤ t →
      (adversarialTranscript gen).output t ∈ adversarialTarget gen ∧
      (adversarialTranscript gen).output t ∉
        observedThrough (adversarialTranscript gen).presentation t) :
    (orderedAdversarialTarget gen).upperDensity
      (scored (adversarialTarget gen) (adversarialTranscript gen).presentation
        (adversarialTranscript gen).output) = 0 := by
  unfold GenLimit.KleinbergWei.OrderedLanguage.upperDensity
  exact (scored_prefixRatio_tendsto_zero gen T hfuture).limsup_eq

lemma negative_claim : NegativeClaim := by
  intro gen hgen
  have hclass := adversarialTarget_mem_class gen
  obtain ⟨T, hfuture⟩ := hgen (adversarialTarget gen) hclass
    (adversarialTranscript gen) (adversarial_protocol gen)
    (adversarial_clean gen) (presentation_injective gen) (adversarial_complete gen)
  refine ⟨adversarialTarget gen, hclass, adversarialPresenter,
    adversarialTranscript gen, orderedAdversarialTarget gen, ?_⟩
  refine ⟨rfl, orderedAdversarialTarget_strictMono gen,
    adversarial_presented gen, adversarial_protocol gen, adversarial_clean gen,
    presentation_injective gen, adversarial_complete gen, ?_⟩
  exact scored_upperDensity_zero gen T hfuture


-- Remaining lemmas establish history coherence, legality, and the density estimate.

end Stage3Proof

open Stage3S2B
open Stage3Proof

theorem stage3_result : Stage3S2B.MainClaim := by
  exact ⟨targetClass_not_countable, uniform_generation, negative_claim⟩
