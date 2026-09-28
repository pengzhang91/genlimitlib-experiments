import Separation

namespace Stage3Case019.PairSweep

open GenLimit
open GenLimit.Generic
open GenLimit.NoiseLossFeedback
open GenLimit.UnionClosedness

inductive Side
  | negative
  | positive
  deriving DecidableEq

def code : Side → ℕ → ℤ
  | .negative => negativeCode
  | .positive => positiveCode

 theorem code_injective (s : Side) : Function.Injective (code s) := by
  cases s
  · exact negativeCode_injective
  · exact positiveCode_injective

 theorem code_ne_other (n m : ℕ) : code .negative n ≠ code .positive m := by
  intro h
  have hn := negativeCode_mem n
  change negativeCode n = positiveCode m at h
  rw [h] at hn
  exact (Int.not_lt_of_ge (Int.ofNat_zero_le _)) hn

structure State where
  seen : Finset ℤ
  made : Finset ℤ
  last : ℤ

def initial : State := ⟨∅, ∅, 0⟩

def pairUntouched (st : State) (s : Side) (p : ℕ) : Prop :=
  code s (2 * p) ∉ st.seen ∧ code s (2 * p + 1) ∉ st.seen ∧
    code s (2 * p) ∉ st.made ∧ code s (2 * p + 1) ∉ st.made

def inPair (s : Side) (x : ℤ) (p : ℕ) : Prop :=
  x = code s (2 * p) ∨ x = code s (2 * p + 1)

private theorem exists_fresh (st : State) (s : Side) (x : ℤ) :
    ∃ n, code s n ∉ insert x st.seen ∧ code s n ∉ st.made := by
  classical
  let bad := (insert x st.seen ∪ st.made).preimage (code s) (code_injective s).injOn
  obtain ⟨N, hN⟩ := Finset.exists_nat_subset_range bad
  refine ⟨N, ?_, ?_⟩
  · intro h
    have hbad : N ∈ bad := by simp [bad, h]
    have := hN hbad
    simp at this
  · intro h
    have hbad : N ∈ bad := by simp [bad, h]
    have := hN hbad
    simp at this

noncomputable def freshIndex (st : State) (s : Side) (x : ℤ) : ℕ := by
  classical
  exact Nat.find (exists_fresh st s x)

 theorem freshIndex_spec (st : State) (s : Side) (x : ℤ) :
    code s (freshIndex st s x) ∉ insert x st.seen ∧
      code s (freshIndex st s x) ∉ st.made := by
  classical
  exact Nat.find_spec (exists_fresh st s x)

noncomputable def chosen (st : State) (s : Side) (x : ℤ) : ℤ := by
  classical
  exact if h : ∃ p, inPair s x p ∧ pairUntouched st s p then
    let p := Classical.choose h
    if x = code s (2 * p) then code s (2 * p + 1)
    else code s (2 * p)
  else code s (freshIndex st s x)

 theorem chosen_is_code (st : State) (s : Side) (x : ℤ) :
    ∃ n, chosen st s x = code s n := by
  classical
  rw [chosen]
  split
  next h =>
    let p := Classical.choose h
    dsimp only
    split
    · exact ⟨2 * p + 1, rfl⟩
    · exact ⟨2 * p, rfl⟩
  next => exact ⟨freshIndex st s x, rfl⟩

 theorem chosen_fresh (st : State) (s : Side) (x : ℤ) :
    chosen st s x ∉ insert x st.seen ∧ chosen st s x ∉ st.made := by
  classical
  rw [chosen]
  split
  next h =>
    let p := Classical.choose h
    have hp := (Classical.choose_spec h).2
    have hxpair := (Classical.choose_spec h).1
    dsimp only
    split
    next hx =>
      constructor
      · simp only [Finset.mem_insert, not_or]
        constructor
        · intro heq
          apply Nat.ne_of_lt (by omega : 2 * p < 2 * p + 1)
          exact code_injective s (hx.symm.trans heq.symm)
        · exact hp.2.1
      · exact hp.2.2.2
    next hx =>
      have hxodd : x = code s (2 * p + 1) := hxpair.resolve_left hx
      constructor
      · simp only [Finset.mem_insert, not_or]
        constructor
        · intro heq
          apply Nat.ne_of_lt (by omega : 2 * p < 2 * p + 1)
          exact code_injective s (heq.trans hxodd)
        · exact hp.1
      · exact hp.2.2.1
  next h => exact freshIndex_spec st s x

noncomputable def sideAfter (q : ℕ) (seen : Finset ℤ) : Side :=
  if omissionMarkerFinset q ⊆ seen then .positive else .negative

noncomputable def step (q : ℕ) (st : State) (x : ℤ) : State :=
  let s := sideAfter q (insert x st.seen)
  let y := chosen st s x
  ⟨insert x st.seen, insert y st.made, y⟩

noncomputable def run (q : ℕ) (xs : List ℤ) : State :=
  xs.foldl (step q) initial

noncomputable def generator (q : ℕ) : Generator ℤ :=
  fun _ xs => (run q (List.ofFn xs)).last

end Stage3Case019.PairSweep

namespace Stage3Case019.PairSweep

noncomputable def traceState (q : ℕ) (input : Stream ℤ) (t : ℕ) : State :=
  run q (List.ofFn fun k : Fin t => input k)

@[simp] theorem traceState_zero (q : ℕ) (input : Stream ℤ) :
    traceState q input 0 = initial := by
  simp [traceState, run]

 theorem traceState_succ (q : ℕ) (input : Stream ℤ) (t : ℕ) :
    traceState q input (t + 1) = step q (traceState q input t) (input t) := by
  rw [traceState, traceState, List.ofFn_succ_last, run, List.foldl_append]
  rfl

 theorem output_eq_last (q : ℕ) (input : Stream ℤ) (t : ℕ) :
    outputAfterInput (generator q) input t = (traceState q input (t + 1)).last := by
  rfl

 theorem sample_succ (f : Stream ℤ) (t : ℕ) :
    GenLimit.Generic.sample f (t + 1) =
      insert (f t) (GenLimit.Generic.sample f t) := by
  classical
  ext x
  simp only [GenLimit.Generic.mem_sample_iff, Finset.mem_insert]
  constructor
  · rintro ⟨s, hs, rfl⟩
    by_cases hst : s = t
    · exact Or.inl (congrArg f hst)
    · exact Or.inr ⟨s, by omega, rfl⟩
  · rintro (rfl | ⟨s, hs, rfl⟩)
    · exact ⟨t, by omega, rfl⟩
    · exact ⟨s, by omega, rfl⟩

 theorem trace_seen (q : ℕ) (input : Stream ℤ) (t : ℕ) :
    (traceState q input t).seen = GenLimit.Generic.sample input t := by
  induction t with
  | zero => simp [traceState_zero, initial, GenLimit.Generic.sample]
  | succ t ih =>
      rw [traceState_succ]
      change insert (input t) (traceState q input t).seen = _
      rw [ih, sample_succ]

 theorem trace_made (q : ℕ) (input : Stream ℤ) (t : ℕ) :
    (traceState q input t).made =
      GenLimit.Generic.sample (outputAfterInput (generator q) input) t := by
  induction t with
  | zero => simp [traceState_zero, initial, GenLimit.Generic.sample]
  | succ t ih =>
      rw [traceState_succ]
      change insert
        (chosen (traceState q input t)
          (sideAfter q (insert (input t) (traceState q input t).seen)) (input t))
        (traceState q input t).made = _
      rw [ih, sample_succ]
      congr 1
      rw [output_eq_last, traceState_succ]
      rfl

 theorem output_fresh (q : ℕ) (input : Stream ℤ) (t : ℕ) :
    let y := outputAfterInput (generator q) input t
    y ∉ GenLimit.Generic.sample input (t + 1) ∧
      ∀ s, s < t → outputAfterInput (generator q) input s ≠ y := by
  rw [output_eq_last, traceState_succ]
  simp only [step]
  let side := sideAfter q (insert (input t) (traceState q input t).seen)
  let y := chosen (traceState q input t) side (input t)
  have hf := chosen_fresh (traceState q input t) side (input t)
  change y ∉ GenLimit.Generic.sample input (t + 1) ∧
    ∀ s, s < t → outputAfterInput (generator q) input s ≠ y
  constructor
  · rw [sample_succ, ← trace_seen q input t]
    simpa [y] using hf.1
  · intro s hs heq
    apply hf.2
    rw [trace_made q input t]
    rw [GenLimit.Generic.mem_sample_iff]
    exact ⟨s, hs, heq⟩

 theorem output_is_side_code (q : ℕ) (input : Stream ℤ) (t : ℕ) :
    ∃ n, outputAfterInput (generator q) input t =
      code (sideAfter q (GenLimit.Generic.sample input (t + 1))) n := by
  rw [output_eq_last, traceState_succ]
  simp only [step]
  rw [sample_succ, ← trace_seen q input t]
  exact chosen_is_code (traceState q input t)
    (sideAfter q (insert (input t) (traceState q input t).seen)) (input t)

 theorem output_injective (q : ℕ) (input : Stream ℤ) :
    Function.Injective (outputAfterInput (generator q) input) := by
  intro s t hst
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact ((output_fresh q input t).2 s hlt) hst
  · exact ((output_fresh q input s).2 t hlt) hst.symm

 theorem output_generatorFirst (q : ℕ) (input : Stream ℤ) (t : ℕ) :
    outputAfterInput (generator q) input t ∈
      GeneratorFirstOn input (outputAfterInput (generator q) input) := by
  refine ⟨t, rfl, ?_⟩
  intro s hs heq
  exact (output_fresh q input t).1
    (GenLimit.Generic.mem_sample_iff.mpr ⟨s, by omega, heq⟩)

end Stage3Case019.PairSweep

namespace Stage3Case019.PairSweep

open GenLimit
open GenLimit.Generic
open GenLimit.NoiseLossFeedback
open GenLimit.UnionClosedness

private theorem injective_eventually_avoids_finset
    {f : ℕ → ℤ} (hf : Function.Injective f) (F : Finset ℤ) :
    ∃ T, ∀ t, T ≤ t → f t ∉ F := by
  classical
  let times := F.preimage f hf.injOn
  obtain ⟨T, hT⟩ := Finset.exists_nat_subset_range times
  refine ⟨T, ?_⟩
  intro t ht hmem
  have htTimes : t ∈ times := by simp [times, hmem]
  have := hT htTimes
  simp at this
  omega

 theorem first_novel_valid
    {q : ℕ} {K : Set ℤ} (hK : K ∈ finiteOmissionFirstClass q)
    {input : Stream ℤ}
    (henum : InjectiveValueContaminatedPresentationAtMost input K q) :
    NovelGeneratesAfterInput input (outputAfterInput (generator q) input) K := by
  classical
  obtain ⟨hmarkers, j, htail⟩ := hK
  obtain ⟨Tm, hTm⟩ := allMarkers_eventually_observed henum hmarkers
  let low : Finset ℤ := (Finset.range j).image positiveCode
  obtain ⟨Tl, hTl⟩ := injective_eventually_avoids_finset
    (output_injective q input) low
  refine ⟨max Tm Tl, ?_⟩
  intro t ht
  have hm : omissionMarkerFinset q ⊆ GenLimit.Generic.sample input (t + 1) := by
    simpa [observedThrough] using hTm t ((Nat.le_max_left _ _).trans ht)
  obtain ⟨n, hn⟩ := output_is_side_code q input t
  have hside : sideAfter q (GenLimit.Generic.sample input (t + 1)) = .positive := by
    simp [sideAfter, hm]
  rw [hside, code] at hn
  have hnlow : n ∉ Finset.range j := by
    intro hnrange
    apply hTl t ((Nat.le_max_right _ _).trans ht)
    exact Finset.mem_image.mpr ⟨n, hnrange, hn.symm⟩
  have hjn : j ≤ n := by simpa using hnlow
  have hmemTail : positiveCode n ∈ positiveTail j := by
    refine ⟨n - j, ?_⟩
    exact congrArg positiveCode (Nat.add_sub_of_le hjn)
  obtain ⟨hfresh, hnew⟩ := output_fresh q input t
  exact ⟨hn ▸ htail hmemTail, hfresh, hnew⟩

 theorem second_novel_valid
    {q : ℕ} {K : Set ℤ} (hK : K ∈ finiteOmissionSecondClass q)
    {input : Stream ℤ}
    (henum : InjectiveValueContaminatedPresentationAtMost input K q) :
    NovelGeneratesAfterInput input (outputAfterInput (generator q) input) K := by
  refine ⟨0, ?_⟩
  intro t _
  have hno : ¬omissionMarkerFinset q ⊆ GenLimit.Generic.sample input (t + 1) := by
    simpa [observedThrough] using not_allMarkers_observed_second hK henum t
  obtain ⟨n, hn⟩ := output_is_side_code q input t
  have hside : sideAfter q (GenLimit.Generic.sample input (t + 1)) = .negative := by
    simp [sideAfter, hno]
  rw [hside, code] at hn
  obtain ⟨hfresh, hnew⟩ := output_fresh q input t
  exact ⟨hn ▸ hK.1 (negativeCode_mem n), hfresh, hnew⟩

end Stage3Case019.PairSweep

namespace Stage3Case019.PairSweep

open GenLimit
open GenLimit.Generic
open GenLimit.NoiseLossFeedback
open GenLimit.UnionClosedness

private theorem inPair_unique {s : Side} {x : ℤ} {p r : ℕ}
    (hp : inPair s x p) (hr : inPair s x r) : p = r := by
  rcases hp with hp | hp <;> rcases hr with hr | hr
  · have := code_injective s (hp.symm.trans hr)
    omega
  · have := code_injective s (hp.symm.trans hr)
    omega
  · have := code_injective s (hp.symm.trans hr)
    omega
  · have := code_injective s (hp.symm.trans hr)
    omega

 theorem chosen_inPair_of
    {st : State} {s : Side} {x : ℤ} {p : ℕ}
    (hx : inPair s x p) (hu : pairUntouched st s p) :
    inPair s (chosen st s x) p := by
  classical
  rw [chosen]
  split
  next h =>
    let r := Classical.choose h
    have hr := (Classical.choose_spec h).1
    have hrp : r = p := inPair_unique hr hx
    dsimp only
    subst r
    split
    · right; simpa [hrp]
    · left; simpa [hrp]
  next h => exact False.elim (h ⟨p, hx, hu⟩)

 theorem pair_secured_at_first
    (q : ℕ) (input : Stream ℤ) (K : Set ℤ)
    (s : Side) (p t : ℕ)
    (hside : sideAfter q (GenLimit.Generic.sample input (t + 1)) = s)
    (hcurrent : inPair s (input t) p)
    (hevenBefore : code s (2 * p) ∉ GenLimit.Generic.sample input t)
    (hoddBefore : code s (2 * p + 1) ∉ GenLimit.Generic.sample input t)
    (hevenK : code s (2 * p) ∈ K)
    (hoddK : code s (2 * p + 1) ∈ K) :
    ∃ z, inPair s z p ∧ z ∈ K ∧
      z ∈ GeneratorFirstOn input (outputAfterInput (generator q) input) := by
  by_cases hevenMade : code s (2 * p) ∈ (traceState q input t).made
  · rw [trace_made] at hevenMade
    obtain ⟨r, hr, hout⟩ := GenLimit.Generic.mem_sample_iff.mp hevenMade
    refine ⟨code s (2 * p), Or.inl rfl, hevenK, ?_⟩
    rw [← hout]
    exact output_generatorFirst q input r
  · by_cases hoddMade : code s (2 * p + 1) ∈ (traceState q input t).made
    · rw [trace_made] at hoddMade
      obtain ⟨r, hr, hout⟩ := GenLimit.Generic.mem_sample_iff.mp hoddMade
      refine ⟨code s (2 * p + 1), Or.inr rfl, hoddK, ?_⟩
      rw [← hout]
      exact output_generatorFirst q input r
    · have hu : pairUntouched (traceState q input t) s p := by
        rw [pairUntouched, trace_seen]
        exact ⟨hevenBefore, hoddBefore, hevenMade, hoddMade⟩
      let y := outputAfterInput (generator q) input t
      have hy : inPair s y p := by
        change inPair s (outputAfterInput (generator q) input t) p
        rw [output_eq_last, traceState_succ]
        simp only [step]
        rw [trace_seen, ← sample_succ, hside]
        exact chosen_inPair_of hcurrent hu
      refine ⟨y, hy, ?_, output_generatorFirst q input t⟩
      rcases hy with hy | hy
      · exact hy ▸ hevenK
      · exact hy ▸ hoddK

theorem first_pair_secured
    {q : ℕ} {K : Set ℤ} (hK : K ∈ finiteOmissionFirstClass q)
    {input : Stream ℤ}
    (henum : InjectiveValueContaminatedPresentationAtMost input K q) :
    ∃ B, ∀ p, B ≤ p →
      ∃ z, inPair .positive z p ∧ z ∈ K ∧
        z ∈ GeneratorFirstOn input (outputAfterInput (generator q) input) := by
  classical
  obtain ⟨hmarkers, j, htail⟩ := hK
  obtain ⟨T, hT⟩ := allMarkers_eventually_observed henum hmarkers
  let oldIndices := (GenLimit.Generic.sample input T).preimage positiveCode
    positiveCode_injective.injOn
  obtain ⟨N, hN⟩ := Finset.exists_nat_subset_range oldIndices
  refine ⟨max j N, ?_⟩
  intro p hp
  have hjp : j ≤ p := (Nat.le_max_left _ _).trans hp
  have hNp : N ≤ p := (Nat.le_max_right _ _).trans hp
  have htarget (n : ℕ) (hn : j ≤ n) : positiveCode n ∈ K := by
    apply htail
    refine ⟨n - j, ?_⟩
    exact congrArg positiveCode (Nat.add_sub_of_le hn)
  obtain ⟨te, hte⟩ := henum.2.1 (htarget (2 * p) (by omega))
  obtain ⟨todd, htodd⟩ := henum.2.1 (htarget (2 * p + 1) (by omega))
  let t := min te todd
  have hTt : T ≤ t := by
    by_contra hnot
    have htT : t < T := Nat.lt_of_not_ge hnot
    rcases min_choice te todd with ht | ht
    · have hteT : te < T := by
        dsimp [t] at htT
        omega
      have hmem : 2 * p ∈ oldIndices := by
        simp only [oldIndices, Finset.mem_preimage]
        rw [GenLimit.Generic.mem_sample_iff]
        exact ⟨te, hteT, hte⟩
      have := hN hmem
      simp at this
      omega
    · have htoddT : todd < T := by
        dsimp [t] at htT
        omega
      have hmem : 2 * p + 1 ∈ oldIndices := by
        simp only [oldIndices, Finset.mem_preimage]
        rw [GenLimit.Generic.mem_sample_iff]
        exact ⟨todd, htoddT, htodd⟩
      have := hN hmem
      simp at this
      omega
  have hcurrent : inPair .positive (input t) p := by
    change input (min te todd) = positiveCode (2 * p) ∨
      input (min te todd) = positiveCode (2 * p + 1)
    rcases min_choice te todd with ht | ht
    · left; rw [ht, hte]
    · right; rw [ht, htodd]
  have hevenBefore : positiveCode (2 * p) ∉ GenLimit.Generic.sample input t := by
    rw [GenLimit.Generic.mem_sample_iff]
    rintro ⟨r, hr, hre⟩
    have : r = te := henum.1 (hre.trans hte.symm)
    omega
  have hoddBefore : positiveCode (2 * p + 1) ∉ GenLimit.Generic.sample input t := by
    rw [GenLimit.Generic.mem_sample_iff]
    rintro ⟨r, hr, hre⟩
    have : r = todd := henum.1 (hre.trans htodd.symm)
    omega
  apply pair_secured_at_first q input K .positive p t
  · have hm : omissionMarkerFinset q ⊆ GenLimit.Generic.sample input (t + 1) := by
      simpa [observedThrough] using hT t hTt
    simp [sideAfter, hm]
  · exact hcurrent
  · exact hevenBefore
  · exact hoddBefore
  · exact htarget (2 * p) (by omega)
  · exact htarget (2 * p + 1) (by omega)

theorem second_pair_secured
    {q : ℕ} {K : Set ℤ} (hK : K ∈ finiteOmissionSecondClass q)
    {input : Stream ℤ}
    (henum : InjectiveValueContaminatedPresentationAtMost input K q) :
    ∀ p, ∃ z, inPair .negative z p ∧ z ∈ K ∧
      z ∈ GeneratorFirstOn input (outputAfterInput (generator q) input) := by
  intro p
  obtain ⟨te, hte⟩ := henum.2.1 (hK.1 (negativeCode_mem (2 * p)))
  obtain ⟨todd, htodd⟩ := henum.2.1 (hK.1 (negativeCode_mem (2 * p + 1)))
  let t := min te todd
  have hcurrent : inPair .negative (input t) p := by
    change input (min te todd) = negativeCode (2 * p) ∨
      input (min te todd) = negativeCode (2 * p + 1)
    rcases min_choice te todd with ht | ht
    · left; rw [ht, hte]
    · right; rw [ht, htodd]
  have hevenBefore : negativeCode (2 * p) ∉ GenLimit.Generic.sample input t := by
    rw [GenLimit.Generic.mem_sample_iff]
    rintro ⟨r, hr, hre⟩
    have : r = te := henum.1 (hre.trans hte.symm)
    omega
  have hoddBefore : negativeCode (2 * p + 1) ∉ GenLimit.Generic.sample input t := by
    rw [GenLimit.Generic.mem_sample_iff]
    rintro ⟨r, hr, hre⟩
    have : r = todd := henum.1 (hre.trans htodd.symm)
    omega
  apply pair_secured_at_first q input K .negative p t
  · have hno : ¬omissionMarkerFinset q ⊆ GenLimit.Generic.sample input (t + 1) := by
      simpa [observedThrough] using not_allMarkers_observed_second hK henum t
    simp [sideAfter, hno]
  · exact hcurrent
  · exact hevenBefore
  · exact hoddBefore
  · exact hK.1 (negativeCode_mem (2 * p))
  · exact hK.1 (negativeCode_mem (2 * p + 1))

end Stage3Case019.PairSweep
