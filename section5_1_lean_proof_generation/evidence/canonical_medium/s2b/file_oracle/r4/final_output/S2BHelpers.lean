import Stage3Model
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.Log
import GenLimit.Paper39_DenseGeneration.Abstract.Density
import Mathlib.Tactic

namespace Stage3Work

open Stage3S2B
open GenLimit.KleinbergWei
open Filter

structure Config (t : ℕ) where
  presentation : Fin t → ℕ
  query : Fin t → Option ℕ
  answer : Fin t → Option Bool
  output : Fin t → ℕ
  admitted : Finset ℕ
  rejected : Finset ℕ

theorem oddThree_not_core (n : ℕ) : 2 * n + 3 ∉ core := by
  rintro ⟨k, hk⟩
  cases k with
  | zero => norm_num at hk
  | succ k =>
      change 2 ^ (k + 1) = 2 * n + 3 at hk
      have heven : Even (2 ^ (k + 1)) := by
        rw [Nat.even_pow]
        exact ⟨by decide, by omega⟩
      rw [hk] at heven
      rcases heven with ⟨m, hm⟩
      omega

theorem exists_free (I R : Finset ℕ) : ∃ z, z ∈ ordinary ∧ z ∉ I ∪ R := by
  obtain ⟨N, hN⟩ := Finset.exists_nat_subset_range (I ∪ R)
  refine ⟨2 * N + 3, oddThree_not_core N, ?_⟩
  intro hz
  have hlt := hN hz
  simp only [Finset.mem_range] at hlt
  omega

noncomputable def leastFree (I R : Finset ℕ) : ℕ := by
  classical exact Nat.find (exists_free I R)

@[simp] theorem leastFree_mem_ordinary (I R : Finset ℕ) : leastFree I R ∈ ordinary := by
  classical exact (Nat.find_spec (exists_free I R)).1

@[simp] theorem leastFree_not_mem (I R : Finset ℕ) : leastFree I R ∉ I ∪ R := by
  classical exact (Nat.find_spec (exists_free I R)).2

noncomputable def nextX {t : ℕ} (c : Config t) : ℕ :=
  if Even t then 2 ^ (t / 2) else leastFree c.admitted c.rejected

noncomputable def nextI {t : ℕ} (c : Config t) : Finset ℕ :=
  if Even t then c.admitted else insert (nextX c) c.admitted

noncomputable def nextQ (gen : FeedbackGenerator) {t : ℕ} (c : Config t) : Option ℕ :=
  gen.query t (Fin.snoc c.presentation (nextX c)) c.answer

noncomputable def nextB (gen : FeedbackGenerator) {t : ℕ} (c : Config t) : Option Bool := by
  classical exact (nextQ gen c).map fun z => decide (z ∈ core ∨ z ∈ nextI c)

noncomputable def queriedR (gen : FeedbackGenerator) {t : ℕ} (c : Config t) : Finset ℕ := by
  classical exact match nextQ gen c with
  | none => c.rejected
  | some z => if z ∈ core ∨ z ∈ nextI c then c.rejected else insert z c.rejected

noncomputable def nextY (gen : FeedbackGenerator) {t : ℕ} (c : Config t) : ℕ :=
  gen.output t (Fin.snoc c.presentation (nextX c)) (Fin.snoc c.answer (nextB gen c))

noncomputable def nextR (gen : FeedbackGenerator) {t : ℕ} (c : Config t) : Finset ℕ := by
  classical exact if nextY gen c ∈ core ∨ nextY gen c ∈ nextI c ∨ nextY gen c ∈ queriedR gen c
  then queriedR gen c else insert (nextY gen c) (queriedR gen c)

noncomputable def advance (gen : FeedbackGenerator) (t : ℕ) (c : Config t) : Config (t+1) := {
  presentation := Fin.snoc c.presentation (nextX c)
  query := Fin.snoc c.query (nextQ gen c)
  answer := Fin.snoc c.answer (nextB gen c)
  output := Fin.snoc c.output (nextY gen c)
  admitted := nextI c
  rejected := nextR gen c
}

noncomputable def config (gen : FeedbackGenerator) : (t : ℕ) → Config t
  | 0 => ⟨Fin.elim0, Fin.elim0, Fin.elim0, Fin.elim0, ∅, ∅⟩
  | t+1 => advance gen t (config gen t)

noncomputable def tr (gen : FeedbackGenerator) : Transcript where
  presentation t := (config gen (t+1)).presentation (Fin.last t)
  query t := (config gen (t+1)).query (Fin.last t)
  answer t := (config gen (t+1)).answer (Fin.last t)
  output t := (config gen (t+1)).output (Fin.last t)

@[simp] theorem config_succ (gen : FeedbackGenerator) (t : ℕ) :
    config gen (t+1) = advance gen t (config gen t) := rfl

@[simp] theorem config_presentation_eq_tr (gen : FeedbackGenerator) (t : ℕ) (i : Fin t) :
    (config gen t).presentation i = (tr gen).presentation i := by
  induction t with
  | zero => exact Fin.elim0 i
  | succ t ih =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rfl
      · simpa [advance] using ih j

@[simp] theorem config_query_eq_tr (gen : FeedbackGenerator) (t : ℕ) (i : Fin t) :
    (config gen t).query i = (tr gen).query i := by
  induction t with
  | zero => exact Fin.elim0 i
  | succ t ih =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rfl
      · simpa [advance] using ih j

@[simp] theorem config_answer_eq_tr (gen : FeedbackGenerator) (t : ℕ) (i : Fin t) :
    (config gen t).answer i = (tr gen).answer i := by
  induction t with
  | zero => exact Fin.elim0 i
  | succ t ih =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rfl
      · simpa [advance] using ih j

@[simp] theorem config_output_eq_tr (gen : FeedbackGenerator) (t : ℕ) (i : Fin t) :
    (config gen t).output i = (tr gen).output i := by
  induction t with
  | zero => exact Fin.elim0 i
  | succ t ih =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rfl
      · simpa [advance] using ih j

noncomputable def K (gen : FeedbackGenerator) : Language :=
  core ∪ {z | ∃ t, z ∈ (config gen t).admitted}

structure Good {t : ℕ} (c : Config t) : Prop where
  admitted_ordinary : ∀ z ∈ c.admitted, z ∈ ordinary
  rejected_ordinary : ∀ z ∈ c.rejected, z ∈ ordinary
  disjoint : Disjoint c.admitted c.rejected

@[simp] theorem nextI_old {t : ℕ} (c : Config t) : c.admitted ⊆ nextI c := by
  classical
  intro z hz
  by_cases ht : Even t
  · simpa [nextI, ht] using hz
  · simp [nextI, ht, hz]

@[simp] theorem queriedR_old (gen : FeedbackGenerator) {t : ℕ} (c : Config t) :
    c.rejected ⊆ queriedR gen c := by
  classical
  intro z hz
  simp only [queriedR]
  split
  · exact hz
  · split_ifs <;> simp [hz]

@[simp] theorem nextR_queried (gen : FeedbackGenerator) {t : ℕ} (c : Config t) :
    queriedR gen c ⊆ nextR gen c := by
  classical
  intro z hz
  simp only [nextR]
  split_ifs <;> simp [hz]

theorem nextI_ordinary {t : ℕ} {c : Config t} (hc : Good c) :
    ∀ z ∈ nextI c, z ∈ ordinary := by
  classical
  intro z hz
  by_cases ht : Even t
  · exact hc.admitted_ordinary z (by simpa [nextI, ht] using hz)
  · simp only [nextI, ht, if_false, Finset.mem_insert] at hz
    rcases hz with rfl | hz
    · simpa [nextX, ht] using leastFree_mem_ordinary c.admitted c.rejected
    · exact hc.admitted_ordinary z hz

theorem nextI_disjoint_oldR {t : ℕ} {c : Config t} (hc : Good c) :
    Disjoint (nextI c) c.rejected := by
  classical
  rw [Finset.disjoint_left]
  intro z hzI hzR
  by_cases ht : Even t
  · exact Finset.disjoint_left.mp hc.disjoint (by simpa [nextI, ht] using hzI) hzR
  · simp only [nextI, ht, if_false, Finset.mem_insert] at hzI
    rcases hzI with rfl | hzI
    · have hzR' : leastFree c.admitted c.rejected ∈ c.rejected := by
        simpa [nextX, ht] using hzR
      exact (leastFree_not_mem c.admitted c.rejected) (by simp [hzR'])
    · exact Finset.disjoint_left.mp hc.disjoint hzI hzR

theorem queriedR_ordinary (gen : FeedbackGenerator) {t : ℕ} {c : Config t} (hc : Good c) :
    ∀ z ∈ queriedR gen c, z ∈ ordinary := by
  classical
  intro z hz
  simp only [queriedR] at hz
  split at hz <;> rename_i hq
  · exact hc.rejected_ordinary z hz
  · split_ifs at hz with hpos
    · exact hc.rejected_ordinary z hz
    · simp only [Finset.mem_insert] at hz
      rcases hz with rfl | hz
      · simpa [ordinary] using fun hzcore => hpos (Or.inl hzcore)
      · exact hc.rejected_ordinary z hz

theorem nextI_disjoint_queriedR (gen : FeedbackGenerator) {t : ℕ} {c : Config t}
    (hc : Good c) : Disjoint (nextI c) (queriedR gen c) := by
  classical
  rw [Finset.disjoint_left]
  intro z hzI hzR
  simp only [queriedR] at hzR
  split at hzR <;> rename_i hq
  · exact Finset.disjoint_left.mp (nextI_disjoint_oldR hc) hzI hzR
  · split_ifs at hzR with hpos
    · exact Finset.disjoint_left.mp (nextI_disjoint_oldR hc) hzI hzR
    · simp only [Finset.mem_insert] at hzR
      rcases hzR with rfl | hzR
      · exact hpos (Or.inr hzI)
      · exact Finset.disjoint_left.mp (nextI_disjoint_oldR hc) hzI hzR

theorem nextR_ordinary (gen : FeedbackGenerator) {t : ℕ} {c : Config t} (hc : Good c) :
    ∀ z ∈ nextR gen c, z ∈ ordinary := by
  classical
  intro z hz
  simp only [nextR] at hz
  split_ifs at hz with hy
  · exact queriedR_ordinary gen hc z hz
  · simp only [Finset.mem_insert] at hz
    rcases hz with rfl | hz
    · simpa [ordinary] using fun hzcore => hy (Or.inl hzcore)
    · exact queriedR_ordinary gen hc z hz

theorem nextI_disjoint_nextR (gen : FeedbackGenerator) {t : ℕ} {c : Config t}
    (hc : Good c) : Disjoint (nextI c) (nextR gen c) := by
  classical
  rw [Finset.disjoint_left]
  intro z hzI hzR
  simp only [nextR] at hzR
  split_ifs at hzR with hy
  · exact Finset.disjoint_left.mp (nextI_disjoint_queriedR gen hc) hzI hzR
  · simp only [Finset.mem_insert] at hzR
    rcases hzR with rfl | hzR
    · exact hy (Or.inr (Or.inl hzI))
    · exact Finset.disjoint_left.mp (nextI_disjoint_queriedR gen hc) hzI hzR

@[simp] theorem good_config (gen : FeedbackGenerator) (t : ℕ) : Good (config gen t) := by
  induction t with
  | zero =>
      constructor
      · intro z hz; exact (Finset.not_mem_empty z hz).elim
      · intro z hz; exact (Finset.not_mem_empty z hz).elim
      · simp [config]
  | succ t ih =>
      rw [config_succ]
      exact ⟨nextI_ordinary ih, nextR_ordinary gen ih, nextI_disjoint_nextR gen ih⟩

@[simp] theorem admitted_step (gen : FeedbackGenerator) (t : ℕ) :
    (config gen t).admitted ⊆ (config gen (t+1)).admitted := by
  simpa [config_succ, advance] using nextI_old (config gen t)

@[simp] theorem rejected_step (gen : FeedbackGenerator) (t : ℕ) :
    (config gen t).rejected ⊆ (config gen (t+1)).rejected := by
  exact fun z hz => nextR_queried gen (config gen t) (queriedR_old gen (config gen t) hz)

theorem admitted_mono (gen : FeedbackGenerator) {t u : ℕ} (htu : t ≤ u) :
    (config gen t).admitted ⊆ (config gen u).admitted := by
  induction u, htu using Nat.le_induction with
  | base => exact fun _ => id
  | succ u htu ih => exact fun z hz => admitted_step gen u (ih hz)

theorem rejected_mono (gen : FeedbackGenerator) {t u : ℕ} (htu : t ≤ u) :
    (config gen t).rejected ⊆ (config gen u).rejected := by
  induction u, htu using Nat.le_induction with
  | base => exact fun _ => id
  | succ u htu ih => exact fun z hz => rejected_step gen u (ih hz)

theorem rejected_not_K (gen : FeedbackGenerator) {t : ℕ} {z : ℕ}
    (hz : z ∈ (config gen t).rejected) : z ∉ K gen := by
  intro hzK
  rcases hzK with hzcore | ⟨u, hzu⟩
  · exact (good_config gen t).rejected_ordinary z hz hzcore
  · by_cases htu : t ≤ u
    · exact Finset.disjoint_left.mp (good_config gen u).disjoint hzu
        (rejected_mono gen htu hz)
    · have hut : u ≤ t := Nat.le_of_lt (Nat.lt_of_not_ge htu)
      exact Finset.disjoint_left.mp (good_config gen t).disjoint
        (admitted_mono gen hut hzu) hz

theorem admitted_mem_K (gen : FeedbackGenerator) {t : ℕ} {z : ℕ}
    (hz : z ∈ (config gen t).admitted) : z ∈ K gen := Or.inr ⟨t, hz⟩

end Stage3Work

namespace Stage3Work

open Stage3S2B

@[simp] theorem tr_presentation (gen : FeedbackGenerator) (t : ℕ) :
    (tr gen).presentation t = nextX (config gen t) := by
  simp [tr, config_succ, advance]
@[simp] theorem tr_query (gen : FeedbackGenerator) (t : ℕ) :
    (tr gen).query t = nextQ gen (config gen t) := by
  simp [tr, config_succ, advance]
@[simp] theorem tr_answer (gen : FeedbackGenerator) (t : ℕ) :
    (tr gen).answer t = nextB gen (config gen t) := by
  simp [tr, config_succ, advance]
@[simp] theorem tr_output (gen : FeedbackGenerator) (t : ℕ) :
    (tr gen).output t = nextY gen (config gen t) := by
  simp [tr, config_succ, advance]

@[simp] theorem K_mem_iff_at_query (gen : FeedbackGenerator) {t z : ℕ}
    (hq : nextQ gen (config gen t) = some z) :
    z ∈ K gen ↔ z ∈ core ∨ z ∈ nextI (config gen t) := by
  constructor
  · intro hzK
    by_contra hpos
    have hzRq : z ∈ queriedR gen (config gen t) := by
      classical
      simp [queriedR, hq, hpos]
    have hzR : z ∈ (config gen (t+1)).rejected := by
      exact nextR_queried gen (config gen t) hzRq
    exact rejected_not_K gen hzR hzK
  · rintro (hzcore | hzI)
    · exact Or.inl hzcore
    · exact admitted_mem_K gen (t := t+1) (by simpa [config_succ, advance] using hzI)

theorem snoc_presentation_eq (gen : FeedbackGenerator) (t : ℕ) :
    Fin.snoc (config gen t).presentation (nextX (config gen t)) =
      (fun i : Fin (t+1) => (tr gen).presentation i) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp
  · simp [advance]

theorem snoc_answer_eq (gen : FeedbackGenerator) (t : ℕ) :
    Fin.snoc (config gen t).answer (nextB gen (config gen t)) =
      (fun i : Fin (t+1) => (tr gen).answer i) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp
  · simp [advance]

@[simp] theorem followsProtocol (gen : FeedbackGenerator) : FollowsProtocol gen (K gen) (tr gen) := by
  intro t
  constructor
  · simp only [tr_query, nextQ]
    rw [snoc_presentation_eq]
    congr 1
    funext i
    exact config_answer_eq_tr gen t i
  constructor
  · classical
    simp only [tr_query, tr_answer]
    unfold nextB
    split <;> rename_i hq
    · simp [hq]
    · rename_i z
      simp only [hq, Option.map_some]
      simp [membershipAnswer, K_mem_iff_at_query gen hq]
  · simp only [tr_output, nextY]
    rw [snoc_presentation_eq, snoc_answer_eq]

@[simp] theorem K_targetClass (gen : FeedbackGenerator) : K gen ∈ targetClass := by
  refine ⟨{z | ∃ t, z ∈ (config gen t).admitted}, ?_, rfl⟩
  intro z hz
  rcases hz with ⟨t, hzt⟩
  exact (good_config gen t).admitted_ordinary z hzt

@[simp] theorem clean (gen : FeedbackGenerator) : Clean (tr gen).presentation (K gen) := by
  intro t
  by_cases ht : Even t
  · left
    rcases ht with ⟨r, rfl⟩
    refine ⟨r, ?_⟩
    simp [nextX]
    congr 1
    omega
  · right
    refine ⟨t+1, ?_⟩
    simp [config_succ, advance, nextI, nextX, ht]

 theorem prior_presentation_assigned (gen : FeedbackGenerator) {s t : ℕ} (hst : s < t) :
    (tr gen).presentation s ∈ core ∨
      (tr gen).presentation s ∈ (config gen t).admitted := by
  by_cases hs : Even s
  · left
    rcases hs with ⟨r, rfl⟩
    refine ⟨r, ?_⟩
    simp [nextX]
    congr 1
    omega
  · right
    have hstep : (tr gen).presentation s ∈ (config gen (s+1)).admitted := by
      simp [config_succ, advance, nextI, nextX, hs]
    exact admitted_mono gen (Nat.succ_le_iff.mpr hst) hstep

theorem presentation_ne_of_lt (gen : FeedbackGenerator) {s t : ℕ} (hst : s < t) :
    (tr gen).presentation s ≠ (tr gen).presentation t := by
  intro heq
  have hassigned := prior_presentation_assigned gen hst
  by_cases ht : Even t
  · have htcore : (tr gen).presentation t ∈ core := by
      rcases ht with ⟨r, rfl⟩
      refine ⟨r, ?_⟩
      simp [nextX]
      congr 1
      omega
    by_cases hs : Even s
    · rcases hs with ⟨a, rfl⟩
      rcases ht with ⟨b, rfl⟩
      have hab : a < b := by omega
      have hexp : (a + a) / 2 = (b + b) / 2 :=
        Nat.pow_right_injective (a := 2) (by omega) (by simpa [nextX] using heq)
      omega
    · have hsord : (tr gen).presentation s ∈ ordinary := by
        simp [tr_presentation, nextX, hs]
      exact hsord (heq ▸ htcore)
  · have htord : (tr gen).presentation t ∈ ordinary := by
      simp [tr_presentation, nextX, ht]
    have htfree : (tr gen).presentation t ∉
        (config gen t).admitted ∪ (config gen t).rejected := by
      simpa [tr_presentation, nextX, ht] using
        leastFree_not_mem (config gen t).admitted (config gen t).rejected
    rcases hassigned with hscore | hsI
    · exact htord (heq ▸ hscore)
    · apply htfree
      simp only [Finset.mem_union]
      left
      rw [← heq]
      exact hsI

 theorem presentation_injective (gen : FeedbackGenerator) :
    Function.Injective (tr gen).presentation := by
  intro s t heq
  rcases lt_trichotomy s t with hst | hst | hts
  · exact (presentation_ne_of_lt gen hst heq).elim
  · exact hst
  · exact (presentation_ne_of_lt gen hts heq.symm).elim

 theorem admitted_was_presented (gen : FeedbackGenerator) {t z : ℕ}
    (hz : z ∈ (config gen t).admitted) : ∃ s, s < t ∧ (tr gen).presentation s = z := by
  induction t with
  | zero => simp [config] at hz
  | succ t ih =>
      classical
      rw [config_succ] at hz
      simp only [advance] at hz
      by_cases ht : Even t
      · have hzold : z ∈ (config gen t).admitted := by simpa [nextI, ht] using hz
        rcases ih hzold with ⟨s, hs, hsz⟩
        exact ⟨s, hs.trans_le (Nat.le_succ t), hsz⟩
      · simp only [nextI, ht, if_false, Finset.mem_insert] at hz
        rcases hz with rfl | hz
        · exact ⟨t, Nat.lt_succ_self t, by simp [nextX, ht]⟩
        · rcases ih hz with ⟨s, hs, hsz⟩
          exact ⟨s, hs.trans_le (Nat.le_succ t), hsz⟩

@[simp] theorem complete (gen : FeedbackGenerator) : Complete (tr gen).presentation (K gen) := by
  intro z hz
  rcases hz with ⟨k, rfl⟩ | ⟨t, hzt⟩
  · refine ⟨2*k, ?_⟩
    simp [nextX]
  · rcases admitted_was_presented gen hzt with ⟨s, hs, hsz⟩
    exact ⟨s, hsz⟩

noncomputable def presenter (gen : FeedbackGenerator) : CausalPresenter where
  next t _ _ _ _ := (tr gen).presentation t

@[simp] theorem presentedBy (gen : FeedbackGenerator) : PresentedBy (presenter gen) (tr gen) := by
  intro t
  rfl

end Stage3Work

namespace Stage3Work

open Stage3S2B
open GenLimit.KleinbergWei
open Filter

 theorem exists_small_free (F : Finset ℕ) :
    ∃ j < F.card + 1, 2*j+3 ∉ F := by
  by_contra h
  push_neg at h
  let f : ℕ → ℕ := fun j => 2*j+3
  have hsub : (Finset.range (F.card+1)).image f ⊆ F := by
    intro z hz
    simp only [Finset.mem_image, Finset.mem_range] at hz
    rcases hz with ⟨j, hj, rfl⟩
    exact h j hj
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ (by intro a b hab; dsimp [f] at hab; omega),
    Finset.card_range] at hcard
  omega

 theorem leastFree_le (I R : Finset ℕ) :
    leastFree I R ≤ 2 * (I ∪ R).card + 3 := by
  classical
  obtain ⟨j, hj, hjfree⟩ := exists_small_free (I ∪ R)
  have hfind : leastFree I R ≤ 2*j+3 :=
    Nat.find_min' (exists_free I R) ⟨oddThree_not_core j, hjfree⟩
  omega

 theorem nextI_card_le {t : ℕ} (c : Config t) :
    (nextI c).card ≤ c.admitted.card + 1 := by
  classical
  by_cases ht : Even t
  · simp [nextI, ht]
  · simpa [nextI, ht] using Finset.card_insert_le (nextX c) c.admitted

 theorem queriedR_card_le (gen : FeedbackGenerator) {t : ℕ} (c : Config t) :
    (queriedR gen c).card ≤ c.rejected.card + 1 := by
  classical
  simp only [queriedR]
  split
  · omega
  · split_ifs
    · omega
    · exact Finset.card_insert_le _ _

 theorem nextR_card_le (gen : FeedbackGenerator) {t : ℕ} (c : Config t) :
    (nextR gen c).card ≤ c.rejected.card + 2 := by
  classical
  calc
    (nextR gen c).card ≤ (queriedR gen c).card + 1 := by
      simp only [nextR]
      split_ifs
      · omega
      · exact Finset.card_insert_le _ _
    _ ≤ c.rejected.card + 2 := by
      have h := queriedR_card_le gen c
      omega

 theorem assigned_card_le (gen : FeedbackGenerator) (t : ℕ) :
    (config gen t).admitted.card + (config gen t).rejected.card ≤ 3*t := by
  induction t with
  | zero => simp [config]
  | succ t ih =>
      rw [config_succ]
      simp only [advance]
      have hI := nextI_card_le (config gen t)
      have hR := nextR_card_le gen (config gen t)
      omega

 theorem odd_presentation_le (gen : FeedbackGenerator) (r : ℕ) :
    (tr gen).presentation (2*r+1) ≤ 12*r+9 := by
  have hodd : ¬ Even (2*r+1) := by
    rintro ⟨k, hk⟩
    omega
  rw [tr_presentation]
  simp only [nextX, hodd, if_false]
  calc
    leastFree (config gen (2*r+1)).admitted (config gen (2*r+1)).rejected
        ≤ 2 * ((config gen (2*r+1)).admitted ∪
          (config gen (2*r+1)).rejected).card + 3 := leastFree_le _ _
    _ ≤ 2 * ((config gen (2*r+1)).admitted.card +
          (config gen (2*r+1)).rejected.card) + 3 := by
      gcongr
      exact Finset.card_union_le _ _
    _ ≤ 12*r+9 := by
      have h := assigned_card_le gen (2*r+1)
      omega

 theorem K_infinite (gen : FeedbackGenerator) : (K gen).Infinite := by
  apply (Set.infinite_range_of_injective (presentation_injective gen)).mono
  exact Set.range_subset_iff.mpr (clean gen)

 theorem K_nth_lt (gen : FeedbackGenerator) (n : ℕ) :
    Nat.nth (fun z => z ∈ K gen) n < 12*n+10 := by
  classical
  apply Nat.nth_lt_of_lt_count
  rw [Nat.count_eq_card_filter_range]
  let f : ℕ → ℕ := fun i => (tr gen).presentation (2*i+1)
  have hsub : (Finset.range (n+1)).image f ⊆
      (Finset.range (12*n+10)).filter (fun z => z ∈ K gen) := by
    intro z hz
    simp only [Finset.mem_image, Finset.mem_range, Finset.mem_filter] at hz ⊢
    rcases hz with ⟨i, hi, rfl⟩
    constructor
    · exact (odd_presentation_le gen i).trans_lt (by omega)
    · exact clean gen (2*i+1)
  have hf : Function.Injective f := by
    intro a b hab
    have hidx : 2*a+1 = 2*b+1 := presentation_injective gen hab
    omega
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ hf, Finset.card_range] at hcard
  omega

noncomputable def orderedK (gen : FeedbackGenerator) : Stage3S2B.OrderedLanguage where
  carrier := K gen
  enumeration := Nat.nth (fun z => z ∈ K gen)
  enumeration_injective := Nat.nth_injective (K_infinite gen)
  range_enumeration := Nat.range_nth_of_infinite (K_infinite gen)

@[simp] theorem orderedK_strict (gen : FeedbackGenerator) :
    InheritsAmbientOrder (orderedK gen) := Nat.nth_strictMono (K_infinite gen)

end Stage3Work

namespace Stage3Work

open Stage3S2B
open GenLimit.KleinbergWei
open Filter

 theorem core_prefixCount_le (gen : FeedbackGenerator) (n : ℕ) :
    (orderedK gen).prefixCount core n ≤ Nat.log2 (12*n+10) + 1 := by
  classical
  let B := 12*n+10
  let e : ℕ → ℕ := fun i => (orderedK gen).enumeration i
  let g : ℕ → ℕ := fun i => Nat.log2 (e i)
  have hsub : ((Finset.range n).filter (fun i => e i ∈ core)).image g ⊆
      Finset.range (Nat.log2 B + 1) := by
    intro k hk
    simp only [Finset.mem_image] at hk
    rcases hk with ⟨i, hi, rfl⟩
    change i ∈ (Finset.range n).filter (fun i => e i ∈ core) at hi
    simp only [Finset.mem_filter, Finset.mem_range] at hi
    have hie : e i < B := by
      dsimp [e, orderedK, B]
      exact (K_nth_lt gen i).trans_le (by omega)
    have hlog : Nat.log2 (e i) ≤ Nat.log2 B := by
      rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
      exact Nat.log_mono_right hie.le
    simp only [Finset.mem_range]
    change Nat.log2 (e i) < Nat.log2 B + 1
    omega
  have hinj : Set.InjOn g
      (↑((Finset.range n).filter (fun i => e i ∈ core)) : Set ℕ) := by
    intro i hi j hj hij
    change i ∈ (Finset.range n).filter (fun i => e i ∈ core) at hi
    change j ∈ (Finset.range n).filter (fun i => e i ∈ core) at hj
    simp only [Finset.mem_filter, Finset.mem_range] at hi hj
    rcases hi.2 with ⟨a, ha⟩
    rcases hj.2 with ⟨b, hb⟩
    dsimp [g] at hij
    have hia : Nat.log2 (e i) = a := by
      rw [← ha, Nat.log2_eq_log_two, Nat.log_pow (by omega)]
    have hib : Nat.log2 (e j) = b := by
      rw [← hb, Nat.log2_eq_log_two, Nat.log_pow (by omega)]
    have hab : a = b := by omega
    apply (orderedK gen).enumeration_injective
    dsimp [e] at ha hb ⊢
    rw [← ha, ← hb, hab]
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_iff.mpr hinj, Finset.card_range] at hcard
  simpa [OrderedLanguage.prefixCount, e] using hcard

 theorem log_linear_le (n : ℕ) (hn : 0 < n) :
    Nat.log2 (12*n+10) + 1 ≤ Nat.log2 n + 6 := by
  have hlin : 12*n+10 ≤ 32*n := by omega
  have hlog : Nat.log2 (12*n+10) ≤ Nat.log2 (32*n) := by
    rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
    exact Nat.log_mono_right hlin
  have hn0 : n ≠ 0 := Nat.ne_of_gt hn
  have h32 : Nat.log2 (32*n) = Nat.log2 n + 5 := by
    rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
    calc
      Nat.log 2 (32*n) = Nat.log 2 (((((n*2)*2)*2)*2)*2) := by congr 1 <;> omega
      _ = Nat.log 2 ((((n*2)*2)*2)*2) + 1 := by rw [Nat.log_mul_base (by omega)]; omega
      _ = Nat.log 2 (((n*2)*2)*2) + 2 := by rw [Nat.log_mul_base (by omega)]; omega
      _ = Nat.log 2 ((n*2)*2) + 3 := by rw [Nat.log_mul_base (by omega)]; omega
      _ = Nat.log 2 (n*2) + 4 := by rw [Nat.log_mul_base (by omega)]; omega
      _ = Nat.log 2 n + 5 := by rw [Nat.log_mul_base (by omega) hn0]
  omega

 theorem core_prefixRatio_tendsto_zero (gen : FeedbackGenerator) :
    Tendsto ((orderedK gen).prefixRatio core) atTop (nhds 0) := by
  have hupper : ∀ᶠ n : ℕ in atTop,
      (orderedK gen).prefixRatio core n ≤
        ((Nat.log2 n : ℝ) + 6) / n := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    simp only [OrderedLanguage.prefixRatio, ne_of_gt hn, if_false]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
    exact_mod_cast (core_prefixCount_le gen n).trans (log_linear_le n hn)
  have htend : Tendsto (fun n : ℕ => ((Nat.log2 n : ℝ) + 6) / n)
      atTop (nhds 0) := by
    have hc : Tendsto (fun n : ℕ => (6 : ℝ) / n) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    simpa [add_div] using GenLimit.tendsto_natLog2_div.add hc
  exact squeeze_zero'
    (Eventually.of_forall fun n => (orderedK gen).prefixRatio_nonneg core n)
    hupper htend

@[simp] theorem core_upperDensity_zero (gen : FeedbackGenerator) :
    (orderedK gen).upperDensity core = 0 :=
  (core_prefixRatio_tendsto_zero gen).limsup_eq

 theorem scored_subset_core (gen : FeedbackGenerator) :
    scored (K gen) (tr gen).presentation (tr gen).output ⊆ core := by
  intro z hz
  rcases hz with ⟨hzK, t, hyt, hzobs⟩
  by_contra hzcore
  have hzNotI : z ∉ nextI (config gen t) := by
    intro hzI
    have hzadm : z ∈ (config gen (t+1)).admitted := by
      simpa [config_succ, advance] using hzI
    rcases admitted_was_presented gen hzadm with ⟨s, hs, hsz⟩
    apply hzobs
    exact ⟨s, by omega, hsz⟩
  have hzR : z ∈ (config gen (t+1)).rejected := by
    rw [config_succ]
    simp only [advance]
    have hy : nextY gen (config gen t) = z := by simpa using hyt
    simp only [nextR]
    by_cases hzRq : z ∈ queriedR gen (config gen t)
    · split_ifs
      · exact hzRq
      · simp [hy, hzRq]
    · have hcond : ¬(nextY gen (config gen t) ∈ core ∨
          nextY gen (config gen t) ∈ nextI (config gen t) ∨
          nextY gen (config gen t) ∈ queriedR gen (config gen t)) := by
        simpa [hy] using not_or_intro hzcore (not_or_intro hzNotI hzRq)
      rw [if_neg hcond]
      simp [hy]
  exact (rejected_not_K gen hzR hzK).elim

@[simp] theorem scored_upperDensity_zero (gen : FeedbackGenerator) :
    (orderedK gen).upperDensity
      (scored (K gen) (tr gen).presentation (tr gen).output) = 0 := by
  apply le_antisymm
  · calc
      _ ≤ (orderedK gen).upperDensity core :=
        (orderedK gen).upperDensity_mono (scored_subset_core gen)
      _ = 0 := core_upperDensity_zero gen
  · exact (orderedK gen).upperDensity_nonneg _

end Stage3Work
