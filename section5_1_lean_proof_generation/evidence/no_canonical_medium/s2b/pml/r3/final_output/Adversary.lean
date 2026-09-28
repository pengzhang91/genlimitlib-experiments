import Stage3Model
import Mathlib.Data.Nat.Nth
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Log.Base

namespace Stage3S2B

open Set Filter
open scoped Topology

private def oddCode (n : ℕ) : ℕ := 2 * n + 3

private theorem oddCode_injective : Function.Injective oddCode := by
  intro a b h
  simp only [oddCode] at h
  omega

private theorem oddCode_ordinary (n : ℕ) : oddCode n ∈ ordinary := by
  intro hcore
  obtain ⟨k, hk⟩ := hcore
  have hodd : Odd (oddCode n) := ⟨n + 1, by simp [oddCode]; omega⟩
  cases k with
  | zero => simp [oddCode] at hk
  | succ k =>
      change 2 ^ (k + 1) = oddCode n at hk
      have heven : Even (2 ^ (k + 1)) := ⟨2 ^ k, by ring⟩
      rw [hk] at heven
      exact (Nat.not_even_iff_odd.mpr hodd) heven

private def queryFinset {t : ℕ} (q : Fin t → Option ℕ) : Finset ℕ :=
  Finset.univ.biUnion fun i => match q i with
    | none => ∅
    | some z => {z}

private theorem queryFinset_card_le {t : ℕ} (q : Fin t → Option ℕ) :
    (queryFinset q).card ≤ t := by
  calc
    (queryFinset q).card ≤ ∑ i : Fin t, (match q i with
      | none => (∅ : Finset ℕ)
      | some z => {z}).card := by
        simpa [queryFinset] using
          (Finset.card_biUnion_le (s := (Finset.univ : Finset (Fin t)))
            (t := fun i => match q i with | none => ∅ | some z => {z}))
    _ ≤ ∑ _i : Fin t, 1 := by
      gcongr with i
      cases q i <;> simp
    _ = t := by simp

private def forbidden {t : ℕ} (x : Fin t → ℕ)
    (q : Fin t → Option ℕ) (y : Fin t → ℕ) : Finset ℕ :=
  (Finset.univ.image x ∪ queryFinset q) ∪ Finset.univ.image y

private theorem forbidden_card_le {t : ℕ} (x : Fin t → ℕ)
    (q : Fin t → Option ℕ) (y : Fin t → ℕ) :
    (forbidden x q y).card ≤ 3 * t := by
  calc
    (forbidden x q y).card ≤
        (Finset.univ.image x ∪ queryFinset q).card +
          (Finset.univ.image y).card := Finset.card_union_le _ _
    _ ≤ ((Finset.univ.image x).card + (queryFinset q).card) +
          (Finset.univ.image y).card := by gcongr; exact Finset.card_union_le _ _
    _ ≤ (t + t) + t := by
      gcongr
      · simpa using (Finset.card_image_le (s := (Finset.univ : Finset (Fin t))) (f := x))
      · exact queryFinset_card_le q
      · simpa using (Finset.card_image_le (s := (Finset.univ : Finset (Fin t))) (f := y))
    _ = 3 * t := by omega

private def pool (t : ℕ) : Finset ℕ :=
  (Finset.range (3 * t + 1)).image oddCode

private theorem pool_card (t : ℕ) : (pool t).card = 3 * t + 1 := by
  rw [pool, Finset.card_image_of_injective _ oddCode_injective]
  simp

private theorem exists_pool_not_forbidden {t : ℕ} (x : Fin t → ℕ)
    (q : Fin t → Option ℕ) (y : Fin t → ℕ) :
    ∃ z ∈ pool t, z ∉ forbidden x q y := by
  apply Finset.exists_mem_not_mem_of_card_lt_card
  rw [pool_card]
  have := forbidden_card_le x q y
  omega

noncomputable def freshOrdinary {t : ℕ} (x : Fin t → ℕ)
    (q : Fin t → Option ℕ) (y : Fin t → ℕ) : ℕ :=
  Classical.choose (exists_pool_not_forbidden x q y)

private theorem freshOrdinary_pool {t : ℕ} (x : Fin t → ℕ)
    (q : Fin t → Option ℕ) (y : Fin t → ℕ) :
    freshOrdinary x q y ∈ pool t :=
  (Classical.choose_spec (exists_pool_not_forbidden x q y)).1

private theorem freshOrdinary_not_forbidden {t : ℕ} (x : Fin t → ℕ)
    (q : Fin t → Option ℕ) (y : Fin t → ℕ) :
    freshOrdinary x q y ∉ forbidden x q y :=
  (Classical.choose_spec (exists_pool_not_forbidden x q y)).2

private theorem freshOrdinary_ordinary {t : ℕ} (x : Fin t → ℕ)
    (q : Fin t → Option ℕ) (y : Fin t → ℕ) :
    freshOrdinary x q y ∈ ordinary := by
  have hp := freshOrdinary_pool x q y
  change freshOrdinary x q y ∈
    (Finset.range (3 * t + 1)).image oddCode at hp
  obtain ⟨n, hn, hnval⟩ := Finset.mem_image.mp hp
  rw [← hnval]
  exact oddCode_ordinary n

private theorem freshOrdinary_le {t : ℕ} (x : Fin t → ℕ)
    (q : Fin t → Option ℕ) (y : Fin t → ℕ) :
    freshOrdinary x q y ≤ 6 * t + 3 := by
  have hp := freshOrdinary_pool x q y
  change freshOrdinary x q y ∈
    (Finset.range (3 * t + 1)).image oddCode at hp
  obtain ⟨n, hn, hnval⟩ := Finset.mem_image.mp hp
  simp only [Finset.mem_range] at hn
  rw [← hnval]
  simp [oddCode]
  omega

noncomputable def presenterValue (t : ℕ) (x : Fin t → ℕ)
    (q : Fin t → Option ℕ) (_a : Fin t → Option Bool)
    (y : Fin t → ℕ) : ℕ :=
  if Even t then freshOrdinary x q y else 2 ^ (t / 2)

structure RoundData where
  presentation : ℕ
  query : Option ℕ
  answer : Option Bool
  output : ℕ

noncomputable def roundData (gen : FeedbackGenerator) (t : ℕ) : RoundData := by
  classical
  let prior : Fin t → RoundData := fun i => roundData gen i
  let xpast : Fin t → ℕ := fun i => (prior i).presentation
  let qpast : Fin t → Option ℕ := fun i => (prior i).query
  let apast : Fin t → Option Bool := fun i => (prior i).answer
  let ypast : Fin t → ℕ := fun i => (prior i).output
  let x := presenterValue t xpast qpast apast ypast
  let xhist : Fin (t + 1) → ℕ := Fin.lastCases x xpast
  let q := gen.query t xhist apast
  let a : Option Bool := match q with
    | none => none
    | some z => some (decide (z ∈ core ∨ ∃ i, xhist i = z))
  let ahist : Fin (t + 1) → Option Bool := Fin.lastCases a apast
  exact ⟨x, q, a, gen.output t xhist ahist⟩
termination_by t

noncomputable def adversaryTranscript (gen : FeedbackGenerator) : Transcript where
  presentation t := (roundData gen t).presentation
  query t := (roundData gen t).query
  answer t := (roundData gen t).answer
  output t := (roundData gen t).output

noncomputable def adversaryPresenter : CausalPresenter where
  next := presenterValue

private theorem roundData_eq (gen : FeedbackGenerator) (t : ℕ) :
    roundData gen t = by
      classical
      let xpast : Fin t → ℕ := fun i => (roundData gen i).presentation
      let qpast : Fin t → Option ℕ := fun i => (roundData gen i).query
      let apast : Fin t → Option Bool := fun i => (roundData gen i).answer
      let ypast : Fin t → ℕ := fun i => (roundData gen i).output
      let x := presenterValue t xpast qpast apast ypast
      let xhist : Fin (t + 1) → ℕ := Fin.lastCases x xpast
      let q := gen.query t xhist apast
      let a : Option Bool := match q with
        | none => none
        | some z => some (decide (z ∈ core ∨ ∃ i, xhist i = z))
      let ahist : Fin (t + 1) → Option Bool := Fin.lastCases a apast
      exact ⟨x, q, a, gen.output t xhist ahist⟩ := by
  rw [roundData]

private theorem presentedBy_adversary (gen : FeedbackGenerator) :
    PresentedBy adversaryPresenter (adversaryTranscript gen) := by
  intro t
  unfold adversaryTranscript adversaryPresenter
  dsimp
  rw [roundData_eq]

end Stage3S2B

namespace Stage3S2B

private noncomputable abbrev advX (gen : FeedbackGenerator) : Stream :=
  (adversaryTranscript gen).presentation
private noncomputable abbrev advQ (gen : FeedbackGenerator) :=
  (adversaryTranscript gen).query
private noncomputable abbrev advA (gen : FeedbackGenerator) :=
  (adversaryTranscript gen).answer
private noncomputable abbrev advY (gen : FeedbackGenerator) : Stream :=
  (adversaryTranscript gen).output

noncomputable def adversaryTarget (gen : FeedbackGenerator) : Language :=
  core ∪ (Set.range (advX gen) ∩ ordinary)

private theorem advX_even (gen : FeedbackGenerator) {t : ℕ} (ht : Even t) :
    advX gen t = freshOrdinary
      (fun i : Fin t => advX gen i) (fun i : Fin t => advQ gen i)
      (fun i : Fin t => advY gen i) := by
  unfold advX adversaryTranscript
  dsimp
  rw [roundData_eq]
  simp [presenterValue, ht, advQ, advY, adversaryTranscript]

private theorem advX_odd (gen : FeedbackGenerator) {t : ℕ} (ht : Odd t) :
    advX gen t = 2 ^ (t / 2) := by
  unfold advX adversaryTranscript
  dsimp
  rw [roundData_eq]
  simp [presenterValue, Nat.not_even_iff_odd.mpr ht]

private theorem advX_mem_core_or_ordinary (gen : FeedbackGenerator) (t : ℕ) :
    advX gen t ∈ core ∨ advX gen t ∈ ordinary := by
  rcases Nat.even_or_odd t with ht | ht
  · right
    rw [advX_even gen ht]
    exact freshOrdinary_ordinary _ _ _
  · left
    rw [advX_odd gen ht]
    exact ⟨t / 2, rfl⟩

private theorem adversaryTarget_mem (gen : FeedbackGenerator) :
    adversaryTarget gen ∈ targetClass := by
  exact ⟨Set.range (advX gen) ∩ ordinary, Set.inter_subset_right, rfl⟩

private theorem adversary_clean (gen : FeedbackGenerator) :
    Clean (advX gen) (adversaryTarget gen) := by
  intro t
  rcases advX_mem_core_or_ordinary gen t with h | h
  · exact Or.inl h
  · exact Or.inr ⟨⟨t, rfl⟩, h⟩

private theorem even_fresh_avoids_x (gen : FeedbackGenerator) {s t : ℕ}
    (hst : s < t) (ht : Even t) : advX gen t ≠ advX gen s := by
  rw [advX_even gen ht]
  intro h
  have hn := freshOrdinary_not_forbidden
    (fun i : Fin t => advX gen i) (fun i => advQ gen i)
    (fun i => advY gen i)
  apply hn
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_image.mpr ⟨⟨s, hst⟩, by simpa using h.symm⟩

private theorem advX_ne_of_lt (gen : FeedbackGenerator) {s t : ℕ}
    (hlt : s < t) : advX gen s ≠ advX gen t := by
  rcases Nat.even_or_odd t with ht | ht
  · exact fun h => even_fresh_avoids_x gen hlt ht h.symm
  · rcases Nat.even_or_odd s with hs | hs
    · have hsOrd : advX gen s ∈ ordinary := by
        rw [advX_even gen hs]
        exact freshOrdinary_ordinary _ _ _
      have htCore : advX gen t ∈ core := by
        rw [advX_odd gen ht]
        exact ⟨t / 2, rfl⟩
      exact fun h => hsOrd (h ▸ htCore)
    · intro h
      rw [advX_odd gen hs, advX_odd gen ht] at h
      have hdiv : s / 2 = t / 2 := Nat.pow_right_injective (by norm_num) h
      obtain ⟨a, rfl⟩ := hs
      obtain ⟨b, rfl⟩ := ht
      simp at hdiv
      omega

private theorem adversary_injective (gen : FeedbackGenerator) :
    Function.Injective (advX gen) := by
  intro s t h
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact advX_ne_of_lt gen hlt h
  · exact advX_ne_of_lt gen hgt h.symm

private theorem adversary_complete (gen : FeedbackGenerator) :
    Complete (advX gen) (adversaryTarget gen) := by
  intro z hz
  rcases hz with hz | ⟨⟨t, rfl⟩, _⟩
  · obtain ⟨k, rfl⟩ := hz
    refine ⟨2 * k + 1, ?_⟩
    have hodd : Odd (2 * k + 1) := ⟨k, rfl⟩
    rw [advX_odd gen hodd]
    congr
    omega
  · exact ⟨t, rfl⟩

private theorem future_avoids_query (gen : FeedbackGenerator) {s t z : ℕ}
    (hst : s < t) (hq : advQ gen s = some z) (hz : z ∈ ordinary) :
    advX gen t ≠ z := by
  rcases Nat.even_or_odd t with ht | ht
  · rw [advX_even gen ht]
    intro heq
    have hn := freshOrdinary_not_forbidden
      (fun i : Fin t => advX gen i) (fun i => advQ gen i)
      (fun i => advY gen i)
    apply hn
    apply Finset.mem_union_left
    apply Finset.mem_union_right
    apply Finset.mem_biUnion.mpr
    refine ⟨⟨s, hst⟩, Finset.mem_univ _, ?_⟩
    simp [hq]
    exact heq
  · have hc : advX gen t ∈ core := by
      rw [advX_odd gen ht]
      exact ⟨t / 2, rfl⟩
    exact fun heq => hz (heq ▸ hc)

private theorem future_avoids_output (gen : FeedbackGenerator) {s t : ℕ}
    (hst : s < t) (hy : advY gen s ∈ ordinary) :
    advX gen t ≠ advY gen s := by
  rcases Nat.even_or_odd t with ht | ht
  · rw [advX_even gen ht]
    intro heq
    have hn := freshOrdinary_not_forbidden
      (fun i : Fin t => advX gen i) (fun i => advQ gen i)
      (fun i => advY gen i)
    apply hn
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨⟨s, hst⟩, by simpa using heq.symm⟩
  · have hc : advX gen t ∈ core := by
      rw [advX_odd gen ht]
      exact ⟨t / 2, rfl⟩
    exact fun heq => hy (heq ▸ hc)

end Stage3S2B

namespace Stage3S2B

noncomputable local instance (p : Prop) : Decidable p := Classical.propDecidable p

private theorem lastCases_advX (gen : FeedbackGenerator) (t : ℕ) :
    Fin.lastCases (advX gen t) (fun i : Fin t => advX gen i) =
      (fun i : Fin (t + 1) => advX gen i) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp
  · simp

private theorem adversaryTarget_iff_seen (gen : FeedbackGenerator)
    {t z : ℕ} (hq : advQ gen t = some z) :
    z ∈ adversaryTarget gen ↔
      z ∈ core ∨ ∃ i : Fin (t + 1), advX gen i = z := by
  constructor
  · rintro (hzcore | ⟨⟨s, hs⟩, hzord⟩)
    · exact Or.inl hzcore
    · right
      by_cases hst : s ≤ t
      · exact ⟨⟨s, Nat.lt_succ_iff.mpr hst⟩, hs⟩
      · have hts : t < s := Nat.lt_of_not_ge hst
        exact False.elim ((future_avoids_query gen hts hq hzord) hs)
  · rintro (hzcore | ⟨i, hi⟩)
    · exact Or.inl hzcore
    · rcases advX_mem_core_or_ordinary gen i with hcore | hord
      · exact Or.inl (hi ▸ hcore)
      · exact Or.inr ⟨⟨i, hi⟩, hi ▸ hord⟩

private theorem advQ_eq (gen : FeedbackGenerator) (t : ℕ) :
    advQ gen t = gen.query t (fun i : Fin (t + 1) => advX gen i)
      (fun i : Fin t => advA gen i) := by
  have hx := presentedBy_adversary gen t
  change advX gen t =
    presenterValue t (fun i : Fin t => advX gen i)
      (fun i => advQ gen i) (fun i => advA gen i)
      (fun i => advY gen i) at hx
  unfold advQ adversaryTranscript
  dsimp
  rw [roundData_eq]
  change gen.query t
    (Fin.lastCases
      (presenterValue t (fun i : Fin t => advX gen i)
        (fun i => advQ gen i) (fun i => advA gen i) (fun i => advY gen i))
      (fun i => advX gen i))
    (fun i => advA gen i) = _
  rw [← hx, lastCases_advX]

private theorem advA_eq (gen : FeedbackGenerator) (t : ℕ) :
    advA gen t = match advQ gen t with
      | none => none
      | some z => some (decide (z ∈ core ∨
          ∃ i : Fin (t + 1), advX gen i = z)) := by
  classical
  have hx := presentedBy_adversary gen t
  change advX gen t =
    presenterValue t (fun i : Fin t => advX gen i)
      (fun i => advQ gen i) (fun i => advA gen i)
      (fun i => advY gen i) at hx
  unfold advA adversaryTranscript
  dsimp
  rw [roundData_eq]
  change (match gen.query t
    (Fin.lastCases
      (presenterValue t (fun i : Fin t => advX gen i)
        (fun i => advQ gen i) (fun i => advA gen i) (fun i => advY gen i))
      (fun i => advX gen i))
    (fun i => advA gen i) with
      | none => none
      | some z => some (decide (z ∈ core ∨ ∃ i : Fin (t + 1),
          (Fin.lastCases
            (presenterValue t (fun i : Fin t => advX gen i)
              (fun i => advQ gen i) (fun i => advA gen i) (fun i => advY gen i))
            (fun i => advX gen i) : Fin (t + 1) → ℕ) i = z))) = _
  rw [← hx]
  simp only [lastCases_advX]
  rw [← advQ_eq]

private theorem advY_eq (gen : FeedbackGenerator) (t : ℕ) :
    advY gen t = gen.output t (fun i : Fin (t + 1) => advX gen i)
      (fun i : Fin (t + 1) => advA gen i) := by
  classical
  have hx := presentedBy_adversary gen t
  change advX gen t =
    presenterValue t (fun i : Fin t => advX gen i)
      (fun i => advQ gen i) (fun i => advA gen i)
      (fun i => advY gen i) at hx
  unfold advY adversaryTranscript
  dsimp
  rw [roundData_eq]
  change gen.output t
    (Fin.lastCases
      (presenterValue t (fun i : Fin t => advX gen i)
        (fun i => advQ gen i) (fun i => advA gen i) (fun i => advY gen i))
      (fun i => advX gen i))
    (Fin.lastCases
      (match gen.query t
        (Fin.lastCases
          (presenterValue t (fun i : Fin t => advX gen i)
            (fun i => advQ gen i) (fun i => advA gen i) (fun i => advY gen i))
          (fun i => advX gen i))
        (fun i => advA gen i) with
        | none => none
        | some z => some (decide (z ∈ core ∨ ∃ i : Fin (t + 1),
            (Fin.lastCases
              (presenterValue t (fun i : Fin t => advX gen i)
                (fun i => advQ gen i) (fun i => advA gen i) (fun i => advY gen i))
              (fun i => advX gen i) : Fin (t + 1) → ℕ) i = z)))
      (fun i => advA gen i)) = _
  rw [← hx]
  simp only [lastCases_advX]
  rw [← advQ_eq]
  congr 1
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa only [Fin.lastCases_last] using (advA_eq gen t).symm
  · simp only [Fin.lastCases_castSucc]
    congr 1

private theorem followsProtocol_adversary (gen : FeedbackGenerator) :
    FollowsProtocol gen (adversaryTarget gen) (adversaryTranscript gen) := by
  intro t
  change advQ gen t = gen.query t (fun i : Fin (t + 1) => advX gen i)
      (fun i : Fin t => advA gen i) ∧
    advA gen t = (match advQ gen t with
      | none => none
      | some z => some (membershipAnswer (adversaryTarget gen) z)) ∧
    advY gen t = gen.output t (fun i : Fin (t + 1) => advX gen i)
      (fun i : Fin (t + 1) => advA gen i)
  constructor
  · exact advQ_eq gen t
  constructor
  · rw [advA_eq]
    cases hq : advQ gen t with
    | none => rfl
    | some z =>
        simp only
        congr 2
        exact propext (adversaryTarget_iff_seen gen hq).symm
  · exact advY_eq gen t

private theorem eventual_outputs_in_core (gen : FeedbackGenerator)
    (hvalid : UniversallyEventuallyValidFresh gen) :
    ∃ T, ∀ t, T ≤ t → advY gen t ∈ core := by
  obtain ⟨T, hT⟩ := hvalid (adversaryTarget gen) (adversaryTarget_mem gen)
    (adversaryTranscript gen) (followsProtocol_adversary gen)
    (adversary_clean gen) (adversary_injective gen) (adversary_complete gen)
  refine ⟨T, fun t ht => ?_⟩
  obtain ⟨hyK, hyfresh⟩ := hT t ht
  rcases hyK with hycore | ⟨⟨s, hs⟩, hyord⟩
  · exact hycore
  · exfalso
    by_cases hst : s ≤ t
    · exact hyfresh ⟨s, hst, hs⟩
    · have hts : t < s := Nat.lt_of_not_ge hst
      exact (future_avoids_output gen hts hyord) hs

private theorem scored_subset_core_union_initial (gen : FeedbackGenerator)
    (hvalid : UniversallyEventuallyValidFresh gen) :
    ∃ T, scored (adversaryTarget gen) (advX gen) (advY gen) ⊆
      core ∪ Set.range (fun i : Fin T => advY gen i) := by
  obtain ⟨T, hT⟩ := eventual_outputs_in_core gen hvalid
  refine ⟨T, ?_⟩
  rintro z ⟨hzK, t, hyt, hznot⟩
  by_cases ht : T ≤ t
  · exact Or.inl (hyt ▸ hT t ht)
  · exact Or.inr ⟨⟨t, Nat.lt_of_not_ge ht⟩, hyt⟩

end Stage3S2B

namespace Stage3S2B

private theorem core_infinite : core.Infinite := by
  exact Set.infinite_range_of_injective
    (fun _ _ h => Nat.pow_right_injective (by norm_num) h)

private theorem adversaryTarget_infinite (gen : FeedbackGenerator) :
    (adversaryTarget gen).Infinite :=
  core_infinite.mono Set.subset_union_left

noncomputable def adversaryOrder (gen : FeedbackGenerator) : OrderedLanguage where
  carrier := adversaryTarget gen
  enumeration := Nat.nth (fun z => z ∈ adversaryTarget gen)
  enumeration_injective :=
    (Nat.nth_strictMono (adversaryTarget_infinite gen)).injective
  range_enumeration := Nat.range_nth_of_infinite (adversaryTarget_infinite gen)

private theorem adversaryOrder_inherits (gen : FeedbackGenerator) :
    InheritsAmbientOrder (adversaryOrder gen) := by
  exact Nat.nth_strictMono (adversaryTarget_infinite gen)

private theorem advX_even_index_le (gen : FeedbackGenerator) (j : ℕ) :
    advX gen (2 * j) ≤ 12 * j + 3 := by
  have heven : Even (2 * j) := ⟨j, by omega⟩
  rw [advX_even gen heven]
  have h := freshOrdinary_le
    (fun i : Fin (2 * j) => advX gen i)
    (fun i : Fin (2 * j) => advQ gen i)
    (fun i : Fin (2 * j) => advY gen i)
  omega

private theorem adversaryOrder_enumeration_le (gen : FeedbackGenerator) (n : ℕ) :
    (adversaryOrder gen).enumeration n ≤ 12 * n + 3 := by
  classical
  let fillers : Finset ℕ :=
    (Finset.range (n + 1)).image (fun j => advX gen (2 * j))
  have hfillers_card : fillers.card = n + 1 := by
    dsimp [fillers]
    rw [Finset.card_image_iff.mpr]
    · simp
    · intro a _ b _ hab
      have hindices := adversary_injective gen hab
      omega
  have hfillers_subset : fillers ⊆
      (Finset.range (12 * n + 4)).filter
        (fun z => z ∈ adversaryTarget gen) := by
    intro z hz
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hz
    simp only [Finset.mem_range] at hj
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · have hle := advX_even_index_le gen j
      omega
    · exact adversary_clean gen (2 * j)
  have hcount : n + 1 ≤
      Nat.count (fun z => z ∈ adversaryTarget gen) (12 * n + 4) := by
    rw [Nat.count_eq_card_filter_range]
    rw [← hfillers_card]
    exact Finset.card_le_card hfillers_subset
  have hnth := Nat.nth_lt_of_lt_count (show n <
      Nat.count (fun z => z ∈ adversaryTarget gen) (12 * n + 4) by omega)
  change Nat.nth (fun z => z ∈ adversaryTarget gen) n ≤ 12 * n + 3
  omega

private theorem adversaryOrder_prefixCount_core_le (gen : FeedbackGenerator) (n : ℕ) :
    (adversaryOrder gen).prefixCount core n ≤
      Nat.log2 (12 * n + 3) + 1 := by
  classical
  let indices := (Finset.range n).filter
    (fun i => (adversaryOrder gen).enumeration i ∈ core)
  let values := indices.image (adversaryOrder gen).enumeration
  let powers := (Finset.range (Nat.log2 (12 * n + 3) + 1)).image
    (fun k => 2 ^ k)
  have hvalues_card : values.card = (adversaryOrder gen).prefixCount core n := by
    rw [show (adversaryOrder gen).prefixCount core n = indices.card by
      rfl]
    exact Finset.card_image_of_injective _
      (adversaryOrder gen).enumeration_injective
  have hsubset : values ⊆ powers := by
    intro z hz
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
    have hirange : i < n := (Finset.mem_filter.mp hi).1 |> Finset.mem_range.mp
    have hicore : (adversaryOrder gen).enumeration i ∈ core :=
      (Finset.mem_filter.mp hi).2
    obtain ⟨k, hk⟩ := hicore
    have hienum : (adversaryOrder gen).enumeration i ≤
        (adversaryOrder gen).enumeration n := by
      exact (adversaryOrder_inherits gen).monotone (Nat.le_of_lt hirange)
    have hpow : 2 ^ k ≤ 12 * n + 3 := by
      change 2 ^ k = (adversaryOrder gen).enumeration i at hk
      rw [hk]
      exact hienum.trans (adversaryOrder_enumeration_le gen n)
    have hklog : k ≤ Nat.log2 (12 * n + 3) :=
      (Nat.le_log2 (by omega)).2 hpow
    exact Finset.mem_image.mpr
      ⟨k, Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hklog), hk⟩
  calc
    (adversaryOrder gen).prefixCount core n = values.card := hvalues_card.symm
    _ ≤ powers.card := Finset.card_le_card hsubset
    _ ≤ Nat.log2 (12 * n + 3) + 1 := by
      simpa [powers] using (Finset.card_image_le (s := Finset.range (Nat.log2 (12 * n + 3) + 1)) (f := fun k => 2 ^ k))

end Stage3S2B

namespace Stage3S2B

open Filter
open scoped Topology
private theorem tendsto_logarithmic_bound :
    Tendsto (fun n : ℕ =>
      (Real.logb 2 (12 * (n : ℝ) + 3) + 1) / (n : ℝ))
      atTop (𝓝 0) := by
  have hx : Tendsto (fun n : ℕ => 12 * (n : ℝ) + 3) atTop atTop := by
    apply tendsto_atTop_mono
      (fun n : ℕ => show (n : ℝ) ≤ 12 * (n : ℝ) + 3 by
        have hn : (0 : ℝ) ≤ n := by positivity
        linarith)
    exact tendsto_natCast_atTop_atTop
  have hlogdiv : Tendsto (fun n : ℕ =>
      Real.logb 2 (12 * (n : ℝ) + 3) /
        (12 * (n : ℝ) + 3)) atTop (𝓝 0) :=
    Real.isLittleO_logb_id_atTop.tendsto_div_nhds_zero.comp hx
  have hlinear : Tendsto (fun n : ℕ =>
      (12 * (n : ℝ) + 3) / (n : ℝ)) atTop (𝓝 12) := by
    have hrecip : Tendsto (fun n : ℕ => (3 : ℝ) / (n : ℝ))
        atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    have h : Tendsto (fun n : ℕ => (12 : ℝ) + 3 / (n : ℝ))
        atTop (𝓝 12) := by simpa using tendsto_const_nhds.add hrecip
    apply h.congr'
    filter_upwards [eventually_ne_atTop 0] with n hn
    field_simp
  have hmain : Tendsto (fun n : ℕ =>
      Real.logb 2 (12 * (n : ℝ) + 3) / (n : ℝ))
      atTop (𝓝 0) := by
    have hprod : Tendsto (fun n : ℕ =>
        (Real.logb 2 (12 * (n : ℝ) + 3) / (12 * (n : ℝ) + 3)) *
          ((12 * (n : ℝ) + 3) / (n : ℝ))) atTop (𝓝 0) := by
      simpa using hlogdiv.mul hlinear
    refine hprod.congr' ?_
    filter_upwards [eventually_ne_atTop 0] with n hn
    have hxpos : (12 * (n : ℝ) + 3) ≠ 0 := by positivity
    field_simp
  have hone : Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ))
      atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hsum : Tendsto (fun n : ℕ =>
      Real.logb 2 (12 * (n : ℝ) + 3) / (n : ℝ) + 1 / (n : ℝ))
      atTop (𝓝 0) := by
    simpa using hmain.add hone
  refine hsum.congr' ?_
  filter_upwards [eventually_ne_atTop 0] with n hn
  field_simp

private theorem adversaryOrder_prefixRatio_core_tendsto_zero
    (gen : FeedbackGenerator) :
    Tendsto ((adversaryOrder gen).prefixRatio core) atTop (𝓝 0) := by
  apply squeeze_zero
    (fun n => (adversaryOrder gen).prefixRatio_nonneg core n)
    (fun n => ?_)
    tendsto_logarithmic_bound
  by_cases hn : n = 0
  · simp [hn]
  · simp only [GenLimit.KleinbergWei.OrderedLanguage.prefixRatio,
      hn, if_false]
    apply div_le_div_of_nonneg_right
    · calc
        ((adversaryOrder gen).prefixCount core n : ℝ) ≤
            (Nat.log2 (12 * n + 3) + 1 : ℕ) := by
          exact_mod_cast adversaryOrder_prefixCount_core_le gen n
        _ ≤ Real.logb 2 (12 * (n : ℝ) + 3) + 1 := by
          norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
            Nat.cast_one]
          convert add_le_add_right (Real.log2_le_logb (12 * n + 3)) 1 using 1 <;>
            norm_num
    · positivity

private theorem adversaryOrder_upperDensity_core_zero
    (gen : FeedbackGenerator) :
    (adversaryOrder gen).upperDensity core = 0 :=
  (adversaryOrder_prefixRatio_core_tendsto_zero gen).limsup_eq

end Stage3S2B

namespace Stage3S2B

private theorem adversaryOrder_scored_density_zero
    (gen : FeedbackGenerator)
    (hvalid : UniversallyEventuallyValidFresh gen) :
    (adversaryOrder gen).upperDensity
      (scored (adversaryTarget gen) (advX gen) (advY gen)) = 0 := by
  obtain ⟨T, hsubset⟩ := scored_subset_core_union_initial gen hvalid
  let initial : Language := Set.range (fun i : Fin T => advY gen i)
  have hinitial : initial.Finite := Set.finite_range _
  have hmono := (adversaryOrder gen).upperDensity_mono hsubset
  have hunion := (adversaryOrder gen).upperDensity_union_le core initial
  have hcore := adversaryOrder_upperDensity_core_zero gen
  have hfinite := (adversaryOrder gen).upperDensity_eq_zero_of_finite hinitial
  have hnonneg := (adversaryOrder gen).upperDensity_nonneg
    (scored (adversaryTarget gen) (advX gen) (advY gen))
  rw [hcore, hfinite] at hunion
  linarith

theorem negativeClaim : NegativeClaim := by
  intro gen hvalid
  refine ⟨adversaryTarget gen, adversaryTarget_mem gen,
    adversaryPresenter, adversaryTranscript gen, adversaryOrder gen, ?_⟩
  refine ⟨rfl, adversaryOrder_inherits gen,
    presentedBy_adversary gen, followsProtocol_adversary gen,
    adversary_clean gen, adversary_injective gen,
    adversary_complete gen, ?_⟩
  exact adversaryOrder_scored_density_zero gen hvalid

end Stage3S2B
