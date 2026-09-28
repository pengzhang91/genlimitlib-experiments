import Stage3Model
import Mathlib.Logic.Equiv.Finset

open Set
open Stage3Case019

namespace Case019Partial

structure KMState where
  seen : Finset ℕ
  said : Finset ℕ
  rounds : ℕ
  last : ℕ

variable (family : ℕ → Set ℕ)

noncomputable def strongCandidate (seen : Finset ℕ) (i : ℕ) : Prop :=
  (seen : Set ℕ) ⊆ family i ∧
    ∀ j, j ≤ i → (seen : Set ℕ) ⊆ family j → family i ⊆ family j

noncomputable def candidates (seen : Finset ℕ) (bound : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (bound + 1)).filter (strongCandidate family seen)

noncomputable def focus (seen : Finset ℕ) (bound : ℕ) : ℕ := by
  classical
  let c := candidates family seen bound
  exact if h : c.Nonempty then c.max' h else 0

noncomputable def chooseFresh
    (hinf : ∀ i, (family i).Infinite) (i : ℕ) (used : Finset ℕ) : ℕ :=
  Classical.choose ((hinf i).exists_not_mem_finset used)

lemma chooseFresh_mem
    (hinf : ∀ i, (family i).Infinite) (i : ℕ) (used : Finset ℕ) :
    chooseFresh family hinf i used ∈ family i :=
  (Classical.choose_spec ((hinf i).exists_not_mem_finset used)).1

lemma chooseFresh_not_mem
    (hinf : ∀ i, (family i).Infinite) (i : ℕ) (used : Finset ℕ) :
    chooseFresh family hinf i used ∉ used :=
  (Classical.choose_spec ((hinf i).exists_not_mem_finset used)).2

noncomputable def step
    (hinf : ∀ i, (family i).Infinite) (state : KMState) (x : ℕ) : KMState := by
  let seen := insert x state.seen
  let i := focus family seen state.rounds
  let y := chooseFresh family hinf i (seen ∪ state.said)
  exact {
    seen := seen
    said := insert y state.said
    rounds := state.rounds + 1
    last := y
  }

noncomputable def initialState : KMState :=
  { seen := ∅, said := ∅, rounds := 0, last := 0 }

noncomputable def run
    (hinf : ∀ i, (family i).Infinite) (history : List ℕ) : KMState :=
  history.foldl (step family hinf) initialState

noncomputable def kmGenerator
    (hinf : ∀ i, (family i).Infinite) : Generator ℕ :=
  fun _ history => (run family hinf (List.ofFn history)).last

lemma run_append
    (hinf : ∀ i, (family i).Infinite) (history : List ℕ) (x : ℕ) :
    run family hinf (history ++ [x]) = step family hinf (run family hinf history) x := by
  simp [run]

lemma run_rounds
    (hinf : ∀ i, (family i).Infinite) (history : List ℕ) :
    (run family hinf history).rounds = history.length := by
  induction history using List.reverseRecOn with
  | nil => simp [run, initialState]
  | append_singleton history x ih =>
      rw [run_append]
      simp [step, ih]

lemma run_seen
    (hinf : ∀ i, (family i).Infinite) (history : List ℕ) :
    (run family hinf history).seen = history.toFinset := by
  induction history using List.reverseRecOn with
  | nil => simp [run, initialState]
  | append_singleton history x ih =>
      rw [run_append]
      simp [step, ih]

lemma output_eq_step_last
    (hinf : ∀ i, (family i).Infinite) (input : Stream ℕ) (t : ℕ) :
    outputAfterInput (kmGenerator family hinf) input t =
      (step family hinf
        (run family hinf (List.ofFn fun i : Fin t => input i))
        (input t)).last := by
  change (run family hinf (List.ofFn fun i : Fin (t + 1) => input i)).last = _
  rw [List.ofFn_succ_last, run_append]
  rfl


lemma history_toFinset_eq_sample (input : Stream ℕ) (t : ℕ) :
    (List.ofFn fun i : Fin t => input i).toFinset =
      GenLimit.Generic.sample input t := by
  classical
  ext x
  simp only [List.mem_toFinset, List.mem_ofFn, GenLimit.Generic.sample,
    Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, i.isLt, hi⟩
  · rintro ⟨i, hit, hi⟩
    exact ⟨⟨i, hit⟩, hi⟩

lemma focus_spec_of_candidate
    (seen : Finset ℕ) (bound k : ℕ)
    (hkbound : k ≤ bound) (hk : strongCandidate family seen k) :
    strongCandidate family seen (focus family seen bound) ∧
      k ≤ focus family seen bound := by
  classical
  have hkmem : k ∈ candidates family seen bound := by
    simp only [candidates, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hk⟩
  have hne : (candidates family seen bound).Nonempty := ⟨k, hkmem⟩
  have hfmem : focus family seen bound ∈ candidates family seen bound := by
    simp [focus, hne, Finset.max'_mem]
  constructor
  · exact (Finset.mem_filter.mp hfmem).2
  · simpa [focus, hne] using Finset.le_max' (candidates family seen bound) k hkmem

lemma step_last_mem_focus
    (hinf : ∀ i, (family i).Infinite) (state : KMState) (x : ℕ) :
    (step family hinf state x).last ∈
      family (focus family (insert x state.seen) state.rounds) := by
  simp [step, chooseFresh_mem]

lemma step_last_fresh_seen
    (hinf : ∀ i, (family i).Infinite) (state : KMState) (x : ℕ) :
    (step family hinf state x).last ∉ insert x state.seen := by
  have h := chooseFresh_not_mem family hinf
    (focus family (insert x state.seen) state.rounds)
    (insert x state.seen ∪ state.said)
  simpa [step] using fun hmem => h (Finset.mem_union_left _ hmem)

lemma step_last_fresh_said
    (hinf : ∀ i, (family i).Infinite) (state : KMState) (x : ℕ) :
    (step family hinf state x).last ∉ state.said := by
  have h := chooseFresh_not_mem family hinf
    (focus family (insert x state.seen) state.rounds)
    (insert x state.seen ∪ state.said)
  simpa [step] using fun hmem => h (Finset.mem_union_right _ hmem)

lemma run_said_mono
    (hinf : ∀ i, (family i).Infinite) (history : List ℕ) (x : ℕ) :
    (run family hinf history).said ⊆
      (run family hinf (history ++ [x])).said := by
  rw [run_append]
  simp [step]

lemma output_mem_later_said
    (hinf : ∀ i, (family i).Infinite) (input : Stream ℕ)
    {s t : ℕ} (hst : s < t) :
    outputAfterInput (kmGenerator family hinf) input s ∈
      (run family hinf (List.ofFn fun i : Fin t => input i)).said := by
  induction t with
  | zero => omega
  | succ t ih =>
      rw [List.ofFn_succ_last, run_append]
      change outputAfterInput (kmGenerator family hinf) input s ∈
        insert
          (step family hinf
            (run family hinf (List.ofFn fun i : Fin t => input i))
            (input t)).last
          (run family hinf (List.ofFn fun i : Fin t => input i)).said
      rw [Finset.mem_insert]
      by_cases h : s = t
      · left
        subst s
        exact output_eq_step_last family hinf input t
      · right
        exact ih (by omega)



lemma run_prefix_rounds
    (hinf : ∀ i, (family i).Infinite) (input : Stream ℕ) (t : ℕ) :
    (run family hinf (List.ofFn fun i : Fin t => input i)).rounds = t := by
  rw [run_rounds]
  simp

lemma run_prefix_seen
    (hinf : ∀ i, (family i).Infinite) (input : Stream ℕ) (t : ℕ) :
    (run family hinf (List.ofFn fun i : Fin t => input i)).seen =
      GenLimit.Generic.sample input t := by
  rw [run_seen, history_toFinset_eq_sample]

lemma insert_sample_eq_sample_succ (input : Stream ℕ) (t : ℕ) :
    insert (input t) (GenLimit.Generic.sample input t) =
      GenLimit.Generic.sample input (t + 1) := by
  classical
  ext x
  simp only [Finset.mem_insert, GenLimit.Generic.sample, Finset.mem_image,
    Finset.mem_range]
  constructor
  · rintro (rfl | ⟨i, hit, rfl⟩)
    · exact ⟨t, by omega, rfl⟩
    · exact ⟨i, by omega, rfl⟩
  · rintro ⟨i, hit, rfl⟩
    by_cases h : i = t
    · left
      subst i
      rfl
    · right
      exact ⟨i, by omega, rfl⟩

lemma generic_sample_eq_sample (input : Stream ℕ) (t : ℕ) :
    GenLimit.Generic.sample input t = GenLimit.sample input t := by
  classical
  ext x
  simp [GenLimit.Generic.sample, GenLimit.sample, Finset.mem_image]

lemma output_not_sample
    (hinf : ∀ i, (family i).Infinite) (input : Stream ℕ) (t : ℕ) :
    outputAfterInput (kmGenerator family hinf) input t ∉
      GenLimit.Generic.sample input (t + 1) := by
  rw [output_eq_step_last]
  have h := step_last_fresh_seen family hinf
    (run family hinf (List.ofFn fun i : Fin t => input i)) (input t)
  rw [run_prefix_seen, insert_sample_eq_sample_succ] at h
  exact h

lemma output_ne_previous
    (hinf : ∀ i, (family i).Infinite) (input : Stream ℕ)
    {s t : ℕ} (hst : s < t) :
    outputAfterInput (kmGenerator family hinf) input s ≠
      outputAfterInput (kmGenerator family hinf) input t := by
  intro heq
  have hold := output_mem_later_said family hinf input hst
  have hfresh := step_last_fresh_said family hinf
    (run family hinf (List.ofFn fun i : Fin t => input i)) (input t)
  rw [← output_eq_step_last family hinf input t] at hfresh
  exact hfresh (heq ▸ hold)

lemma sample_subset_of_presents
    {input : Stream ℕ} {K : Set ℕ}
    (hp : GenLimit.Generic.Presents input K) (t : ℕ) :
    (GenLimit.Generic.sample input t : Set ℕ) ⊆ K := by
  intro x hx
  simp only [GenLimit.Generic.sample, Finset.mem_coe, Finset.mem_image,
    Finset.mem_range] at hx
  obtain ⟨i, _, rfl⟩ := hx
  rw [← hp]
  exact ⟨i, rfl⟩

lemma eliminate_prior
    {input : Stream ℕ} {K : Set ℕ}
    (hp : GenLimit.Generic.Presents input K) (k : ℕ) :
    ∃ T, ∀ t, T ≤ t → ∀ j, j < k →
      (GenLimit.Generic.sample input (t + 1) : Set ℕ) ⊆ family j →
      K ⊆ family j := by
  induction k with
  | zero =>
      exact ⟨0, by omega⟩
  | succ k ih =>
      obtain ⟨T, hT⟩ := ih
      by_cases hsub : K ⊆ family k
      · refine ⟨T, ?_⟩
        intro t ht j hj hcons
        by_cases hjk : j = k
        · simpa [hjk] using hsub
        · exact hT t ht j (by omega) hcons
      · obtain ⟨x, hxK, hxnot⟩ := Set.not_subset.mp hsub
        have hxrange : x ∈ Set.range input := by
          rw [hp]
          exact hxK
        obtain ⟨r, hr⟩ := hxrange
        refine ⟨max T r, ?_⟩
        intro t ht j hj hcons
        by_cases hjk : j = k
        · subst j
          exfalso
          apply hxnot
          apply hcons
          simp only [GenLimit.Generic.sample, Finset.mem_coe, Finset.mem_image,
            Finset.mem_range]
          exact ⟨r, by omega, hr⟩
        · exact hT t (by omega) j (by omega) hcons

lemma actual_strong_candidate
    (hinf : ∀ i, (family i).Infinite)
    {input : Stream ℕ} (k : ℕ)
    (hp : GenLimit.Generic.Presents input (family k)) :
    ∃ T, ∀ t, T ≤ t →
      strongCandidate family (GenLimit.Generic.sample input (t + 1)) k := by
  obtain ⟨T, hT⟩ := eliminate_prior family hp k
  refine ⟨T, ?_⟩
  intro t ht
  constructor
  · exact sample_subset_of_presents hp (t + 1)
  · intro j hj hcons
    by_cases hjk : j = k
    · simpa [hjk]
    · exact hT t ht j (by omega) hcons

lemma eventual_output_mem_exact
    (hinf : ∀ i, (family i).Infinite)
    {input : Stream ℕ} (k : ℕ)
    (hp : GenLimit.Generic.Presents input (family k)) :
    ∃ T, ∀ t, T ≤ t →
      outputAfterInput (kmGenerator family hinf) input t ∈ family k := by
  obtain ⟨T, hstrong⟩ := actual_strong_candidate family hinf k hp
  refine ⟨max T k, ?_⟩
  intro t ht
  let state := run family hinf (List.ofFn fun i : Fin t => input i)
  have hrounds : state.rounds = t := run_prefix_rounds family hinf input t
  have hseen : insert (input t) state.seen =
      GenLimit.Generic.sample input (t + 1) := by
    rw [show state.seen = GenLimit.Generic.sample input t from
      run_prefix_seen family hinf input t]
    exact insert_sample_eq_sample_succ input t
  have hfocus := focus_spec_of_candidate family
    (insert (input t) state.seen) state.rounds k (by omega)
    (by simpa [hseen] using hstrong t (by omega))
  rw [output_eq_step_last]
  have hout := step_last_mem_focus family hinf state (input t)
  exact hfocus.1.2 k hfocus.2 (by
    rw [hseen]
    exact sample_subset_of_presents hp (t + 1)) hout

/-- Checked milestone: the finite-history generator is eventually valid and
novel on every exact presentation of every infinite member of an indexed
countable family. -/
theorem countable_exact_eventual_novel
    (family : LanguageFamily ℕ) (hinf : ∀ i, (family i).Infinite) :
    ∃ gen : Generator ℕ, ∀ i (input : Stream ℕ),
      GenLimit.Generic.Presents input (family i) →
      GenLimit.NovelGeneratesInLimit
        input (outputAfterInput gen input) (family i) := by
  refine ⟨kmGenerator family hinf, ?_⟩
  intro i input hp
  obtain ⟨T, hvalid⟩ := eventual_output_mem_exact family hinf i hp
  refine ⟨T, ?_⟩
  intro t ht
  refine ⟨hvalid t ht, ?_, fun s hst => output_ne_previous family hinf input hst⟩
  rw [← generic_sample_eq_sample]
  exact output_not_sample family hinf input t


noncomputable def decodeFinset (code : ℕ) : Finset ℕ :=
  (Encodable.decode code : Option (Finset ℕ)).getD ∅

lemma decodeFinset_encode (F : Finset ℕ) :
    decodeFinset (Encodable.encode F) = F := by
  simp [decodeFinset, Encodable.encodek]

noncomputable def contaminatedFamily
    (family : LanguageFamily ℕ) : LanguageFamily ℕ :=
  fun n => family (Nat.unpair n).1 ∪
    (decodeFinset (Nat.unpair n).2 : Set ℕ)

lemma contaminatedFamily_infinite
    (family : LanguageFamily ℕ) (hinf : ∀ i, (family i).Infinite) :
    ∀ n, (contaminatedFamily family n).Infinite := by
  intro n
  exact (hinf (Nat.unpair n).1).mono (Set.subset_union_left)

lemma range_eq_target_union_difference
    {input : Stream ℕ} {K : Set ℕ} (hcover : K ⊆ Set.range input) :
    Set.range input = K ∪ (Set.range input \ K) := by
  ext x
  constructor
  · intro hx
    by_cases hxK : x ∈ K
    · exact Or.inl hxK
    · exact Or.inr ⟨hx, hxK⟩
  · rintro (hx | hx)
    · exact hcover hx
    · exact hx.1

lemma contaminatedFamily_represents_range
    (family : LanguageFamily ℕ) {input : Stream ℕ} (i : ℕ) (F : Finset ℕ)
    (hcover : family i ⊆ Set.range input)
    (hF : (F : Set ℕ) = Set.range input \ family i) :
    contaminatedFamily family (Nat.pair i (Encodable.encode F)) =
      Set.range input := by
  rw [contaminatedFamily, Nat.unpair_pair, decodeFinset_encode]
  symm
  rw [range_eq_target_union_difference hcover, ← hF]

lemma outputs_injective
    (family : LanguageFamily ℕ) (hinf : ∀ i, (family i).Infinite)
    (input : Stream ℕ) :
    Function.Injective (outputAfterInput (kmGenerator family hinf) input) := by
  intro s t hst
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact output_ne_previous family hinf input hlt hst
  · exact output_ne_previous family hinf input hgt hst.symm

lemma eventually_avoids_finset
    (family : LanguageFamily ℕ) (hinf : ∀ i, (family i).Infinite)
    (input : Stream ℕ) (F : Finset ℕ) :
    ∃ T, ∀ t, T ≤ t →
      outputAfterInput (kmGenerator family hinf) input t ∉ F := by
  let out := outputAfterInput (kmGenerator family hinf) input
  have hout : Function.Injective out := outputs_injective family hinf input
  have hpre : (out ⁻¹' (F : Set ℕ)).Finite :=
    F.finite_toSet.preimage hout.injOn
  obtain ⟨B, hB⟩ := hpre.bddAbove
  refine ⟨B + 1, ?_⟩
  intro t ht htF
  have htpre : t ∈ out ⁻¹' (F : Set ℕ) := htF
  have := hB htpre
  omega

/-- Checked milestone: every indexed countable family of infinite natural
languages has one eventually valid-and-novel generator at every fixed finite
distinct-value contamination level.  This is the validity part of M1; the
half-density strengthening remains open in this artifact. -/
theorem countable_contaminated_eventual_novel (q : ℕ) :
    ∀ family : LanguageFamily ℕ,
      (∀ i, (family i).Infinite) →
        ∃ gen : Generator ℕ,
          ∀ i (input : Stream ℕ),
            GenLimit.Generic.InjectiveValueContaminatedPresentationAtMost
                input (family i) q →
              GenLimit.NovelGeneratesInLimit
                input (outputAfterInput gen input) (family i) := by
  intro family hinf
  let enlarged := contaminatedFamily family
  have henlarged : ∀ n, (enlarged n).Infinite :=
    contaminatedFamily_infinite family hinf
  refine ⟨kmGenerator enlarged henlarged, ?_⟩
  intro i input hp
  rcases hp with ⟨_, hcover, F, hF, _⟩
  let code := Nat.pair i (Encodable.encode F)
  have hrange : enlarged code = Set.range input := by
    exact contaminatedFamily_represents_range family i F hcover hF
  have hpExact : GenLimit.Generic.Presents input (enlarged code) := by
    exact hrange.symm
  obtain ⟨Tvalid, hvalid⟩ :=
    eventual_output_mem_exact enlarged henlarged code hpExact
  obtain ⟨Tavoid, havoid⟩ :=
    eventually_avoids_finset enlarged henlarged input F
  refine ⟨max Tvalid Tavoid, ?_⟩
  intro t ht
  have houtEnlarged := hvalid t (by omega)
  have houtAvoid := havoid t (by omega)
  have houtRange : outputAfterInput (kmGenerator enlarged henlarged) input t ∈
      Set.range input := by simpa [hrange] using houtEnlarged
  have houtTarget : outputAfterInput (kmGenerator enlarged henlarged) input t ∈
      family i := by
    by_contra houtNot
    have : outputAfterInput (kmGenerator enlarged henlarged) input t ∈
        Set.range input \ family i := ⟨houtRange, houtNot⟩
    rw [← hF] at this
    exact houtAvoid this
  refine ⟨houtTarget, ?_, ?_⟩
  · rw [← generic_sample_eq_sample]
    exact output_not_sample enlarged henlarged input t
  · intro s hst
    exact output_ne_previous enlarged henlarged input hst

end Case019Partial
