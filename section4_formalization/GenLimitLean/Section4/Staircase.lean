import Mathlib.Data.List.Range
import Mathlib.Data.Finset.Card
import Mathlib.Data.Set.Finite.Basic
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Finset.Lattice.Fold

/-! Exact staircase frontier: semantic ordered-history model.
Indices start at zero. The common finite commonPrefix of target i has size s i;
its private infinite component consists of pairs (i,r). Strictly increasing
positive commonPrefix sizes encode arbitrary positive finite block sizes. -/
namespace Section4.Staircase

abbrev Point := ℕ ⊕ (ℕ × ℕ)
abbrev History := List Point
abbrev Generator := History → Point

structure Family where
  size : ℕ → ℕ
  positive : 0 < size 0
  increasing : StrictMono size

namespace Family

variable (F : Family)

def target (i : ℕ) : Set Point
  | .inl n => n < F.size i
  | .inr q => q.1 = i

@[simp] theorem mem_target_inl (i n : ℕ) : Sum.inl n ∈ F.target i ↔ n < F.size i := Iff.rfl
@[simp] theorem mem_target_inr (i j r : ℕ) : Sum.inr (j,r) ∈ F.target i ↔ j = i := Iff.rfl

def commonPrefix (i : ℕ) : Finset Point :=
  (Finset.range (F.size i)).map ⟨Sum.inl, Sum.inl_injective⟩

def canonical (i : ℕ) : History :=
  (List.range (F.size i)).map Sum.inl

def Compatible (h : History) (i : ℕ) : Prop := ∀ p ∈ h, p ∈ F.target i

def Legal (i : ℕ) (h : History) : Prop := h.Nodup ∧ F.Compatible h i

def Fresh (G : Generator) : Prop := ∀ h, G h ∉ h

def Boundary (h : History) (k : ℕ) : Prop := h.toFinset = F.commonPrefix k

def Safe (h : History) (p : Point) : Prop :=
  p ∉ h ∧ ∀ i, F.Compatible h i → p ∈ F.target i

@[simp] theorem mem_prefix_inl (i n : ℕ) :
    Sum.inl n ∈ F.commonPrefix i ↔ n < F.size i := by simp [commonPrefix]
@[simp] theorem mem_prefix_inr (i j r : ℕ) :
    Sum.inr (j,r) ∉ F.commonPrefix i := by simp [commonPrefix]
@[simp] theorem prefix_card (i : ℕ) : (F.commonPrefix i).card = F.size i := by simp [commonPrefix]
@[simp] theorem canonical_length (i : ℕ) : (F.canonical i).length = F.size i := by simp [canonical]
@[simp] theorem canonical_finset (i : ℕ) : (F.canonical i).toFinset = F.commonPrefix i := by
  ext p
  cases p <;> simp [canonical, commonPrefix]

theorem canonical_legal (i : ℕ) : F.Legal i (F.canonical i) := by
  constructor
  · exact List.nodup_range.map Sum.inl_injective
  · intro p hp
    cases p with
    | inl n => simpa [canonical, target] using hp
    | inr q => simp [canonical] at hp

theorem boundary_length {h : History} {k : ℕ} (hn : h.Nodup)
    (hb : F.Boundary h k) : h.length = F.size k := by
  simpa only [List.toFinset_card_of_nodup hn, prefix_card] using congrArg Finset.card hb

theorem boundary_unique {h : History} {j k : ℕ}
    (hj : F.Boundary h j) (hk : F.Boundary h k) : j = k := by
  apply F.increasing.injective
  simpa using congrArg Finset.card (hj.symm.trans hk)

theorem boundary_compatible_iff {h : History} {k i : ℕ}
    (hb : F.Boundary h k) : F.Compatible h i ↔ k ≤ i := by
  constructor
  · intro hc
    by_contra hn
    have hik : i < k := by omega
    have hm : Sum.inl (F.size i) ∈ h := by
      rw [← List.mem_toFinset, hb, F.mem_prefix_inl]
      exact F.increasing hik
    have := hc _ hm
    simp [target] at this
  · intro hki p hp
    have hp' : p ∈ F.commonPrefix k := by rw [← hb]; simpa using hp
    cases p with
    | inl n => exact lt_of_lt_of_le ((F.mem_prefix_inl k n).mp hp') (F.increasing.monotone hki)
    | inr q => rcases q with ⟨j,r⟩; exact False.elim (F.mem_prefix_inr k j r hp')

theorem exists_fresh_private (F : Family) (h : History) (i : ℕ) :
    ∃ r, Sum.inr (i,r) ∉ h := by
  have hinf : Set.Infinite (Set.range (fun r : ℕ => (Sum.inr (i,r) : Point))) :=
    Set.infinite_range_of_injective (by intro a b hab; simpa using hab)
  obtain ⟨p, ⟨r, rfl⟩, hp⟩ := hinf.exists_notMem_finset h.toFinset
  exact ⟨r, by simpa using hp⟩

theorem safe_or_boundary (h : History) (hc : ∃ i, F.Compatible h i) :
    (∃ p, F.Safe h p) ∨ ∃ k, F.Boundary h k := by
  classical
  by_cases hp : ∃ i r, Sum.inr (i,r) ∈ h
  · obtain ⟨i,r,hr⟩ := hp
    obtain ⟨r',hr'⟩ := F.exists_fresh_private h i
    left
    refine ⟨Sum.inr (i,r'), hr', ?_⟩
    intro j hj
    exact hj (Sum.inr (i,r)) hr
  · let k := Nat.find hc
    have hk : F.Compatible h k := Nat.find_spec hc
    by_cases hm : ∃ n, n < F.size k ∧ Sum.inl n ∉ h
    · obtain ⟨n,hn,hfresh⟩ := hm
      left
      refine ⟨Sum.inl n,hfresh,?_⟩
      intro i hi
      exact lt_of_lt_of_le hn (F.increasing.monotone (Nat.find_min' hc hi))
    · right
      refine ⟨k,?_⟩
      ext p
      cases p with
      | inl n =>
        simp only [List.mem_toFinset, mem_prefix_inl]
        constructor
        · exact hk _
        · intro hn
          by_contra hnmem
          exact hm ⟨n,hn,hnmem⟩
      | inr q =>
        rcases q with ⟨i,r⟩
        simp only [List.mem_toFinset, mem_prefix_inr, iff_false]
        intro hr
        exact hp ⟨i,r,hr⟩

noncomputable def boundaryIndex (h : History) (hb : ∃ k, F.Boundary h k) : ℕ :=
  Classical.choose hb

noncomputable def scheduleGenerator (σ : ℕ → Bool) (h : History) : Point := by
  classical
  exact if hb : ∃ k, F.Boundary h k then
    let k := F.boundaryIndex h hb
    if σ k then Sum.inr (k,0) else Sum.inl (F.size k)
  else if hs : ∃ p, F.Safe h p then Classical.choose hs
  else Sum.inr (0, Classical.choose (F.exists_fresh_private h 0))

theorem schedule_at_boundary (σ : ℕ → Bool) {h : History} {k : ℕ}
    (hb : F.Boundary h k) :
    F.scheduleGenerator σ h = if σ k then Sum.inr (k,0) else Sum.inl (F.size k) := by
  classical
  have hb' : ∃ k, F.Boundary h k := ⟨k,hb⟩
  have hk : F.boundaryIndex h hb' = k :=
    F.boundary_unique (Classical.choose_spec hb') hb
  unfold scheduleGenerator
  rw [dif_pos hb']
  simp only [hk]

theorem schedule_fresh (σ : ℕ → Bool) : Fresh (F.scheduleGenerator σ) := by
  classical
  intro h
  by_cases hb : ∃ k, F.Boundary h k
  · obtain ⟨k,hk⟩ := hb
    rw [F.schedule_at_boundary σ hk, ← List.mem_toFinset, hk]
    split <;> simp
  · unfold scheduleGenerator
    simp only [dif_neg hb]
    split_ifs with hs
    · exact (Classical.choose_spec hs).1
    · exact Classical.choose_spec (F.exists_fresh_private h 0)

def Charged (σ : ℕ → Bool) (i k : ℕ) : Prop :=
  (k < i ∧ σ k = true) ∨ (k = i ∧ σ i = false)

theorem schedule_error_iff_boundary (σ : ℕ → Bool) {i : ℕ} {h : History}
    (hl : F.Legal i h) :
    F.scheduleGenerator σ h ∉ F.target i ↔ ∃ k, F.Boundary h k ∧ Charged σ i k := by
  classical
  by_cases hb : ∃ k, F.Boundary h k
  · obtain ⟨k,hk⟩ := hb
    have hki := (F.boundary_compatible_iff hk).mp hl.2
    rw [F.schedule_at_boundary σ hk]
    have hchar : ((if σ k then Sum.inr (k,0) else Sum.inl (F.size k)) ∉ F.target i) ↔ Charged σ i k := by
      by_cases hEq : k = i
      · subst k
        cases hs : σ i <;> simp [target, Charged, hs]
      · have hlt : k < i := by omega
        have hsizes := F.increasing hlt
        cases hs : σ k <;> simp [target, Charged, hs, hEq, hlt, hsizes]
    rw [hchar]
    constructor
    · exact fun he => ⟨k,hk,he⟩
    · rintro ⟨j,hj,he⟩
      simpa [F.boundary_unique hj hk] using he
  · have hs : ∃ p, F.Safe h p := (F.safe_or_boundary h ⟨i,hl.2⟩).resolve_right hb
    have hv : F.scheduleGenerator σ h ∈ F.target i := by
      unfold scheduleGenerator
      simp only [dif_neg hb, dif_pos hs]
      exact (Classical.choose_spec hs).2 i hl.2
    simp only [hv, not_true_eq_false, false_iff, not_exists, not_and]
    intro k hk
    exact False.elim (hb ⟨k,hk⟩)



noncomputable def errorIndices (σ : ℕ → Bool) (i : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (i+1)).filter (Charged σ i)

noncomputable def mistakeCount (σ : ℕ → Bool) (i : ℕ) : ℕ := (errorIndices σ i).card

noncomputable def deadline (σ : ℕ → Bool) (i : ℕ) : ℕ :=
  (errorIndices σ i).sup fun k => F.size k + 1

noncomputable def mistakeTimes (G : Generator) (i : ℕ) (h : History) : Finset ℕ := by
  classical
  exact (Finset.range (h.length+1)).filter fun t => G (h.take t) ∉ F.target i

def MistakeBound (G : Generator) (i m : ℕ) : Prop :=
  ∀ h, F.Legal i h → (F.mistakeTimes G i h).card ≤ m

def DeadlineBound (G : Generator) (i d : ℕ) : Prop :=
  ∀ h, F.Legal i h → d ≤ h.length → G h ∈ F.target i

@[simp] theorem mem_errorIndices (σ : ℕ → Bool) (i k : ℕ) :
    k ∈ errorIndices σ i ↔ Charged σ i k := by
  simp only [errorIndices, Finset.mem_filter, Finset.mem_range]
  constructor
  · exact And.right
  · intro h; exact ⟨by rcases h with ⟨h,_⟩ | ⟨h,_⟩ <;> omega,h⟩

theorem charged_le {σ : ℕ → Bool} {i k : ℕ} (h : Charged σ i k) : k ≤ i := by
  rcases h with ⟨h,_⟩ | ⟨h,_⟩ <;> omega

theorem legal_take {h : History} {i : ℕ} (hl : F.Legal i h) (t : ℕ) :
    F.Legal i (h.take t) := by
  exact ⟨hl.1.take, fun p hp => hl.2 p (List.mem_of_mem_take hp)⟩

theorem canonical_take {k i : ℕ} (hki : k ≤ i) :
    (F.canonical i).take (F.size k) = F.canonical k := by
  simp only [canonical, ← List.map_take, List.take_range, Nat.min_eq_left (F.increasing.monotone hki)]

theorem canonical_legal_of_le {k i : ℕ} (hki : k ≤ i) : F.Legal i (F.canonical k) := by
  refine ⟨(F.canonical_legal k).1,?_⟩
  exact (F.boundary_compatible_iff (by simp [Boundary])).mpr hki

theorem schedule_mistakeTimes_subset (σ : ℕ → Bool) {i : ℕ} {h : History}
    (hl : F.Legal i h) :
    F.mistakeTimes (F.scheduleGenerator σ) i h ⊆ (errorIndices σ i).image F.size := by
  classical
  intro t ht
  simp only [mistakeTimes, Finset.mem_filter, Finset.mem_range] at ht
  obtain ⟨k,hk,hcharge⟩ := (F.schedule_error_iff_boundary σ (F.legal_take hl t)).mp ht.2
  have hlength := F.boundary_length (F.legal_take hl t).1 hk
  have htle : t ≤ h.length := by omega
  rw [List.length_take, Nat.min_eq_left htle] at hlength
  exact Finset.mem_image.mpr ⟨k,(mem_errorIndices σ i k).mpr hcharge,hlength.symm⟩

theorem schedule_mistakeBound (σ : ℕ → Bool) (i : ℕ) :
    F.MistakeBound (F.scheduleGenerator σ) i (mistakeCount σ i) := by
  classical
  intro h hl
  calc
    _ ≤ ((errorIndices σ i).image F.size).card := Finset.card_le_card (F.schedule_mistakeTimes_subset σ hl)
    _ = _ := Finset.card_image_of_injective _ F.increasing.injective

theorem schedule_deadlineBound (σ : ℕ → Bool) (i : ℕ) :
    F.DeadlineBound (F.scheduleGenerator σ) i (F.deadline σ i) := by
  intro h hl hd
  by_contra he
  obtain ⟨k,hk,hcharge⟩ := (F.schedule_error_iff_boundary σ hl).mp he
  have hlen := F.boundary_length hl.1 hk
  have hb : F.size k + 1 ≤ F.deadline σ i :=
    Finset.le_sup (f := fun k => F.size k + 1) ((mem_errorIndices σ i k).mpr hcharge)
  omega

theorem schedule_canonical_error (σ : ℕ → Bool) {k i : ℕ} (hk : Charged σ i k) :
    F.scheduleGenerator σ (F.canonical k) ∉ F.target i := by
  apply (F.schedule_error_iff_boundary σ (F.canonical_legal_of_le (charged_le hk))).mpr
  exact ⟨k,by simp [Boundary],hk⟩

theorem charged_times_subset {G : Generator} {σ : ℕ → Bool} {i : ℕ}
    (he : ∀ k, Charged σ i k → G (F.canonical k) ∉ F.target i) :
    (errorIndices σ i).image F.size ⊆ F.mistakeTimes G i (F.canonical i) := by
  classical
  intro t ht
  obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp ht
  have hc := (mem_errorIndices σ i k).mp hk
  simp only [mistakeTimes, Finset.mem_filter, Finset.mem_range, canonical_length]
  exact ⟨by have := F.increasing.monotone (charged_le hc); omega,
    by rw [F.canonical_take (charged_le hc)]; exact he k hc⟩

theorem mistakeBound_lower {G : Generator} {σ : ℕ → Bool} {i m : ℕ}
    (he : ∀ k, Charged σ i k → G (F.canonical k) ∉ F.target i)
    (hm : F.MistakeBound G i m) : mistakeCount σ i ≤ m := by
  classical
  calc
    _ = ((errorIndices σ i).image F.size).card :=
      (Finset.card_image_of_injective _ F.increasing.injective).symm
    _ ≤ (F.mistakeTimes G i (F.canonical i)).card := Finset.card_le_card (F.charged_times_subset he)
    _ ≤ _ := hm _ (F.canonical_legal i)

theorem deadlineBound_lower {G : Generator} {σ : ℕ → Bool} {i d : ℕ}
    (he : ∀ k, Charged σ i k → G (F.canonical k) ∉ F.target i)
    (hd : F.DeadlineBound G i d) : F.deadline σ i ≤ d := by
  apply Finset.sup_le
  intro k hk
  have hc := (mem_errorIndices σ i k).mp hk
  have hnot := he k hc
  have hlt : F.size k < d := by
    by_contra hn
    exact hnot (hd _ (F.canonical_legal_of_le (charged_le hc)) (by simpa using Nat.le_of_not_gt hn))
  omega

theorem schedule_mistakeBound_iff (σ : ℕ → Bool) (i m : ℕ) :
    F.MistakeBound (F.scheduleGenerator σ) i m ↔ mistakeCount σ i ≤ m := by
  constructor
  · exact F.mistakeBound_lower (fun _ hk => F.schedule_canonical_error σ hk)
  · intro hm h hl
    exact (F.schedule_mistakeBound σ i h hl).trans hm

theorem schedule_deadlineBound_iff (σ : ℕ → Bool) (i d : ℕ) :
    F.DeadlineBound (F.scheduleGenerator σ) i d ↔ F.deadline σ i ≤ d := by
  constructor
  · exact F.deadlineBound_lower (fun _ hk => F.schedule_canonical_error σ hk)
  · intro hd h hl hh
    exact F.schedule_deadlineBound σ i h hl (hd.trans hh)

noncomputable def extractedSchedule (G : Generator) (k : ℕ) : Bool := by
  classical
  exact decide (∃ r, G (F.canonical k) = Sum.inr (k,r))

theorem extracted_charged_error {G : Generator} (hf : Fresh G) {i k : ℕ}
    (hc : Charged (F.extractedSchedule G) i k) : G (F.canonical k) ∉ F.target i := by
  classical
  have hf' : G (F.canonical k) ∉ F.commonPrefix k := by
    simpa only [← F.canonical_finset k, List.mem_toFinset] using hf (F.canonical k)
  rcases hc with ⟨hki,hσ⟩ | ⟨hki,hσ⟩
  · have hex : ∃ r, G (F.canonical k) = Sum.inr (k,r) := by
      simpa [extractedSchedule] using hσ
    obtain ⟨r,hr⟩ := hex
    rw [hr]
    simp [target, Nat.ne_of_lt hki]
  · subst k
    have hn : ¬ ∃ r, G (F.canonical i) = Sum.inr (i,r) := by
      simpa [extractedSchedule] using hσ
    cases hg : G (F.canonical i) with
    | inl n => simpa [target, hg] using hf'
    | inr q =>
      rcases q with ⟨j,r⟩
      intro hji
      change j = i at hji
      subst j
      exact hn ⟨r,hg⟩

/-- One schedule simultaneously improves every finite mistake and deadline
bound of an arbitrary deterministic fresh ordered-history generator. -/
theorem arbitrary_generator_domination (G : Generator) (hf : Fresh G) :
    ∃ σ : ℕ → Bool, ∀ i,
      (∀ m, F.MistakeBound G i m → mistakeCount σ i ≤ m) ∧
      (∀ d, F.DeadlineBound G i d → F.deadline σ i ≤ d) := by
  refine ⟨F.extractedSchedule G, fun i => ⟨?_,?_⟩⟩
  · exact fun m hm => F.mistakeBound_lower (fun _ hk => F.extracted_charged_error hf hk) hm
  · exact fun d hd => F.deadlineBound_lower (fun _ hk => F.extracted_charged_error hf hk) hd

end Family
end Section4.Staircase
