import Stage3Model
import Mathlib.Data.Nat.Log

open Filter
open scoped Topology

namespace Case025Proof

open Stage3Case025

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

def Consistent (family : ℕ → Language) (seen : Finset ℕ) (i : ℕ) : Prop :=
  ∀ x ∈ seen, x ∈ family i

noncomputable def criticalIndices
    (family : ℕ → Language) (seen : Finset ℕ) : ℕ → Finset ℕ
  | 0 => if Consistent family seen 0 then {0} else ∅
  | n + 1 =>
      let previous := criticalIndices family seen n
      if Consistent family seen (n + 1) ∧
          ∀ j ∈ previous, family (n + 1) ⊆ family j then
        insert (n + 1) previous
      else previous

def ExhaustedBelow
    (family : ℕ → Language) (announced : Finset ℕ) (i bound : ℕ) : Prop :=
  ∀ x, x ∈ family i → x ∉ announced →
    2 ^ bound ≤ GenLimit.PatientScope.prefixCount (family i) x

noncomputable def patientIndices
    (family : ℕ → Language) (seen announced : Finset ℕ) : ℕ → Finset ℕ
  | 0 => if 0 ∈ criticalIndices family seen 0 then {0} else ∅
  | n + 1 =>
      let previous := patientIndices family seen announced n
      if n + 1 ∈ criticalIndices family seen (n + 1) ∧
          ∀ h : previous.Nonempty,
            ExhaustedBelow family announced (previous.max' h) (n + 1) then
        insert (n + 1) previous
      else previous

def focusIndex
    (family : ℕ → Language) (seen announced : Finset ℕ) (bound : ℕ) : ℕ :=
  if h : (patientIndices family seen announced bound).Nonempty then
    (patientIndices family seen announced bound).max' h
  else 0

def focusLanguage
    (family : ℕ → Language) (seen announced : Finset ℕ) (bound : ℕ) : Language :=
  if (patientIndices family seen announced bound).Nonempty then
    family (focusIndex family seen announced bound)
  else Set.univ

noncomputable def leastFresh (S : Set ℕ) (announced : Finset ℕ) : ℕ := by
  classical
  exact if h : ∃ x, x ∈ S ∧ x ∉ announced then Nat.find h else 0

noncomputable def patientGenerator (family : ℕ → Language) : OnlineGenerator :=
  fun t input output =>
    let inputSeen := Finset.univ.image input
    let announced := inputSeen ∪ Finset.univ.image output
    leastFresh (focusLanguage family inputSeen announced t) announced

lemma leastFresh_mem {S : Set ℕ} {announced : Finset ℕ}
    (h : ∃ x, x ∈ S ∧ x ∉ announced) : leastFresh S announced ∈ S := by
  classical
  rw [leastFresh, dif_pos h]
  exact (Nat.find_spec h).1

lemma leastFresh_not_mem {S : Set ℕ} {announced : Finset ℕ}
    (h : ∃ x, x ∈ S ∧ x ∉ announced) : leastFresh S announced ∉ announced := by
  classical
  rw [leastFresh, dif_pos h]
  exact (Nat.find_spec h).2

lemma leastFresh_le {S : Set ℕ} {announced : Finset ℕ} {x : ℕ}
    (hxS : x ∈ S) (hx : x ∉ announced) : leastFresh S announced ≤ x := by
  classical
  have h : ∃ y, y ∈ S ∧ y ∉ announced := ⟨x, hxS, hx⟩
  rw [leastFresh, dif_pos h]
  exact Nat.find_min' h ⟨hxS, hx⟩

lemma infinite_has_fresh {S : Set ℕ} (hS : S.Infinite) (announced : Finset ℕ) :
    ∃ x, x ∈ S ∧ x ∉ announced := by
  simpa [and_assoc] using hS.exists_notMem_finset announced


lemma prefixFinset_mono {S : Set ℕ} {a b : ℕ} (hab : a ≤ b) :
    GenLimit.PatientScope.prefixFinset S a ⊆
      GenLimit.PatientScope.prefixFinset S b := by
  intro x hx
  simp only [GenLimit.PatientScope.prefixFinset, Finset.mem_filter,
    Finset.mem_range] at hx ⊢
  exact ⟨hx.1.trans_le hab, hx.2⟩

lemma prefixCount_mono {S : Set ℕ} :
    Monotone (GenLimit.PatientScope.prefixCount S) := by
  intro a b hab
  exact Finset.card_le_card (prefixFinset_mono hab)

lemma prefixCount_strict_of_mem {S : Set ℕ} {a b : ℕ}
    (hab : a < b) (ha : a ∈ S) :
    GenLimit.PatientScope.prefixCount S a <
      GenLimit.PatientScope.prefixCount S b := by
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨prefixFinset_mono hab.le, ?_⟩
  intro heq
  have ha_mem : a ∈ GenLimit.PatientScope.prefixFinset S b := by
    simp [GenLimit.PatientScope.prefixFinset, hab, ha]
  rw [← heq] at ha_mem
  simpa [GenLimit.PatientScope.prefixFinset] using ha_mem

lemma prefixCount_injective_on {S : Set ℕ} :
    Set.InjOn (GenLimit.PatientScope.prefixCount S) S := by
  intro a ha b hb heq
  rcases lt_trichotomy a b with hab | rfl | hba
  · exact (ne_of_lt (prefixCount_strict_of_mem hab ha)) heq |>.elim
  · rfl
  · exact (ne_of_gt (prefixCount_strict_of_mem hba hb)) heq |>.elim

lemma exhausted_mono_announced
    (family : ℕ → Language) {a b : Finset ℕ} {i bound : ℕ}
    (hab : a ⊆ b) (h : ExhaustedBelow family a i bound) :
    ExhaustedBelow family b i bound := by
  intro x hx hxb
  exact h x hx (fun hxa => hxb (hab hxa))


lemma bounded_monotone_finset_eventually_constant
    {α : Type*} [DecidableEq α] (f : ℕ → Finset α) (B : Finset α)
    (hmono : Monotone f) (hbound : ∀ n, f n ⊆ B) :
    ∃ N, ∀ n, N ≤ n → f n = f N := by
  classical
  let U := B.filter (fun x => ∃ n, x ∈ f n)
  let first : α → ℕ := fun x => if h : ∃ n, x ∈ f n then Nat.find h else 0
  let N := U.sup first
  refine ⟨N, fun n hn => Finset.Subset.antisymm ?_ (hmono hn)⟩
  intro x hx
  have hxB : x ∈ B := hbound n hx
  have hxU : x ∈ U := by
    simp only [U, Finset.mem_filter]
    exact ⟨hxB, ⟨n, hx⟩⟩
  have hex : ∃ k, x ∈ f k := ⟨n, hx⟩
  have hfirst : x ∈ f (first x) := by
    simp only [first, dif_pos hex]
    exact Nat.find_spec hex
  have hfirstN : first x ≤ N := Finset.le_sup hxU
  exact hmono hfirstN hfirst

def inputSeenAt (input : Stream) (t : ℕ) : Finset ℕ :=
  Finset.univ.image (fun i : Fin (t + 1) => input i)

def outputSeenAt (output : Stream) (t : ℕ) : Finset ℕ :=
  Finset.univ.image (fun i : Fin t => output i)

def announcedAt (input output : Stream) (t : ℕ) : Finset ℕ :=
  inputSeenAt input t ∪ outputSeenAt output t

lemma inputSeenAt_mono (input : Stream) : Monotone (inputSeenAt input) := by
  intro a b hab x hx
  rcases Finset.mem_image.mp hx with ⟨i, -, rfl⟩
  apply Finset.mem_image.mpr
  exact ⟨⟨i, by omega⟩, Finset.mem_univ _, rfl⟩

lemma outputSeenAt_mono (output : Stream) : Monotone (outputSeenAt output) := by
  intro a b hab x hx
  rcases Finset.mem_image.mp hx with ⟨i, -, rfl⟩
  apply Finset.mem_image.mpr
  exact ⟨⟨i, by omega⟩, Finset.mem_univ _, rfl⟩

lemma announcedAt_mono (input output : Stream) :
    Monotone (announcedAt input output) := by
  intro a b hab
  exact Finset.union_subset_union (inputSeenAt_mono input hab)
    (outputSeenAt_mono output hab)


noncomputable def separatingPoint (K S : Set ℕ) : ℕ :=
  if h : K ⊆ S then 0 else Nat.find (Set.not_subset.mp h)

lemma separatingPoint_mem_left {K S : Set ℕ} (h : ¬K ⊆ S) :
    separatingPoint K S ∈ K := by
  rw [separatingPoint, dif_neg h]
  exact (Nat.find_spec (Set.not_subset.mp h)).1

lemma separatingPoint_not_mem_right {K S : Set ℕ} (h : ¬K ⊆ S) :
    separatingPoint K S ∉ S := by
  rw [separatingPoint, dif_neg h]
  exact (Nat.find_spec (Set.not_subset.mp h)).2

noncomputable def firstOccurrence (input : Stream) (x : ℕ) : ℕ :=
  if h : ∃ t, input t = x then Nat.find h else 0

lemma firstOccurrence_spec {input : Stream} {x : ℕ} (h : ∃ t, input t = x) :
    input (firstOccurrence input x) = x := by
  rw [firstOccurrence, dif_pos h]
  exact Nat.find_spec h

noncomputable def criticalThreshold
    (family : ℕ → Language) (input : Stream) (i : ℕ) : ℕ :=
  (Finset.range i).sup fun j =>
    firstOccurrence input (separatingPoint (family i) (family j))

lemma presents_input_mem {input : Stream} {K : Language}
    (hp : GenLimit.Presents input K) (t : ℕ) : input t ∈ K := by
  rw [← hp]
  exact ⟨t, rfl⟩

lemma presents_exists_eq {input : Stream} {K : Language}
    (hp : GenLimit.Presents input K) {x : ℕ} (hx : x ∈ K) :
    ∃ t, input t = x := by
  rw [← hp] at hx
  rcases hx with ⟨t, rfl⟩
  exact ⟨t, rfl⟩

lemma target_consistent
    (family : ℕ → Language) {input : Stream} {i t : ℕ}
    (hp : GenLimit.Presents input (family i)) :
    Consistent family (inputSeenAt input t) i := by
  intro x hx
  rcases Finset.mem_image.mp hx with ⟨s, -, rfl⟩
  exact presents_input_mem hp s

lemma lower_consistent_contains_target
    (family : ℕ → Language) {input : Stream} {i t j : ℕ}
    (hp : GenLimit.Presents input (family i))
    (ht : criticalThreshold family input i ≤ t) (hj : j < i)
    (hcons : Consistent family (inputSeenAt input t) j) :
    family i ⊆ family j := by
  by_contra hsub
  let x := separatingPoint (family i) (family j)
  have hxK : x ∈ family i := separatingPoint_mem_left hsub
  have hxnot : x ∉ family j := separatingPoint_not_mem_right hsub
  have hex : ∃ s, input s = x := presents_exists_eq hp hxK
  let s := firstOccurrence input x
  have hs_eq : input s = x := firstOccurrence_spec hex
  have hs_le_threshold : s ≤ criticalThreshold family input i := by
    apply Finset.le_sup (s := Finset.range i) (f := fun k =>
      firstOccurrence input (separatingPoint (family i) (family k)))
    simpa [s, x] using hj
  have hxseen : x ∈ inputSeenAt input t := by
    apply Finset.mem_image.mpr
    refine ⟨⟨s, by omega⟩, Finset.mem_univ _, ?_⟩
    exact hs_eq
  exact hxnot (hcons x hxseen)


lemma criticalIndices_subset_range
    (family : ℕ → Language) (seen : Finset ℕ) (n : ℕ) :
    criticalIndices family seen n ⊆ Finset.range (n + 1) := by
  induction n with
  | zero =>
      by_cases h : Consistent family seen 0 <;> simp [criticalIndices, h]
  | succ n ih =>
      by_cases h : Consistent family seen (n + 1) ∧
          ∀ j ∈ criticalIndices family seen n, family (n + 1) ⊆ family j
      · simp only [criticalIndices, if_pos h]
        exact Finset.insert_subset_iff.mpr
          ⟨by simp, ih.trans (Finset.range_mono (Nat.le_succ _))⟩
      · simp only [criticalIndices, if_neg h]
        exact ih.trans (Finset.range_mono (Nat.le_succ _))

lemma criticalIndices_step_mono
    (family : ℕ → Language) (seen : Finset ℕ) (n : ℕ) :
    criticalIndices family seen n ⊆ criticalIndices family seen (n + 1) := by
  by_cases h : Consistent family seen (n + 1) ∧
      ∀ j ∈ criticalIndices family seen n, family (n + 1) ⊆ family j
  · rw [criticalIndices, if_pos h]
    exact Finset.subset_insert (n + 1) _
  · rw [criticalIndices, if_neg h]

lemma patientIndices_subset_range
    (family : ℕ → Language) (seen announced : Finset ℕ) (n : ℕ) :
    patientIndices family seen announced n ⊆ Finset.range (n + 1) := by
  induction n with
  | zero =>
      by_cases h : 0 ∈ criticalIndices family seen 0 <;> simp [patientIndices, h]
  | succ n ih =>
      by_cases h : n + 1 ∈ criticalIndices family seen (n + 1) ∧
          ∀ hne : (patientIndices family seen announced n).Nonempty,
            ExhaustedBelow family announced
              ((patientIndices family seen announced n).max' hne) (n + 1)
      · simp only [patientIndices, if_pos h]
        exact Finset.insert_subset_iff.mpr
          ⟨by simp, ih.trans (Finset.range_mono (Nat.le_succ _))⟩
      · simp only [patientIndices, if_neg h]
        exact ih.trans (Finset.range_mono (Nat.le_succ _))

lemma patientIndices_step_mono
    (family : ℕ → Language) (seen announced : Finset ℕ) (n : ℕ) :
    patientIndices family seen announced n ⊆
      patientIndices family seen announced (n + 1) := by
  by_cases h : n + 1 ∈ criticalIndices family seen (n + 1) ∧
      ∀ hne : (patientIndices family seen announced n).Nonempty,
        ExhaustedBelow family announced
          ((patientIndices family seen announced n).max' hne) (n + 1)
  · simp [patientIndices, h]
  · simp [patientIndices, h]

lemma patientIndices_subset_criticalIndices
    (family : ℕ → Language) (seen announced : Finset ℕ) (n : ℕ) :
    patientIndices family seen announced n ⊆ criticalIndices family seen n := by
  induction n with
  | zero =>
      by_cases h : 0 ∈ criticalIndices family seen 0 <;> simp [patientIndices, h]
  | succ n ih =>
      have hcrit := criticalIndices_step_mono family seen n
      by_cases h : n + 1 ∈ criticalIndices family seen (n + 1) ∧
          ∀ hne : (patientIndices family seen announced n).Nonempty,
            ExhaustedBelow family announced
              ((patientIndices family seen announced n).max' hne) (n + 1)
      · simp only [patientIndices, if_pos h]
        exact Finset.insert_subset_iff.mpr ⟨h.1, ih.trans hcrit⟩
      · simp only [patientIndices, if_neg h]
        exact ih.trans hcrit


lemma criticalIndices_mem_consistent
    (family : ℕ → Language) (seen : Finset ℕ) {n j : ℕ}
    (hj : j ∈ criticalIndices family seen n) : Consistent family seen j := by
  induction n generalizing j with
  | zero =>
      by_cases h : Consistent family seen 0
      · have hj0 : j = 0 := by simpa [criticalIndices, h] using hj
        subst j
        exact h
      · simp [criticalIndices, h] at hj
  | succ n ih =>
      by_cases h : Consistent family seen (n + 1) ∧
          ∀ k ∈ criticalIndices family seen n, family (n + 1) ⊆ family k
      · rw [criticalIndices, if_pos h] at hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · exact h.1
        · exact ih hj
      · rw [criticalIndices, if_neg h] at hj
        exact ih hj

lemma criticalIndices_chain
    (family : ℕ → Language) (seen : Finset ℕ) {n j k : ℕ}
    (hj : j ∈ criticalIndices family seen n)
    (hk : k ∈ criticalIndices family seen n) (hjk : j ≤ k) :
    family k ⊆ family j := by
  induction n generalizing j k with
  | zero =>
      have hj0 : j = 0 := by
        have := criticalIndices_subset_range family seen 0 hj
        simpa using this
      have hk0 : k = 0 := by
        have := criticalIndices_subset_range family seen 0 hk
        simpa using this
      simpa [hj0, hk0]
  | succ n ih =>
      by_cases h : Consistent family seen (n + 1) ∧
          ∀ r ∈ criticalIndices family seen n, family (n + 1) ⊆ family r
      · rw [criticalIndices, if_pos h] at hj hk
        rcases Finset.mem_insert.mp hk with rfl | hk
        · rcases Finset.mem_insert.mp hj with rfl | hj
          · exact Set.Subset.rfl
          · exact h.2 j hj
        · rcases Finset.mem_insert.mp hj with rfl | hj
          · have hk_le : k ≤ n := by
              have := criticalIndices_subset_range family seen n hk
              have : k < n + 1 := by simpa [Finset.mem_range] using this
              omega
            omega
          · exact ih hj hk hjk
      · rw [criticalIndices, if_neg h] at hj hk
        exact ih hj hk hjk

lemma criticalIndices_mem_le
    (family : ℕ → Language) (seen : Finset ℕ) {n j : ℕ}
    (hj : j ∈ criticalIndices family seen n) : j ≤ n := by
  have hlt : j < n + 1 := by
    simpa [Finset.mem_range] using criticalIndices_subset_range family seen n hj
  omega

lemma patientIndices_mem_le
    (family : ℕ → Language) (seen announced : Finset ℕ) {n j : ℕ}
    (hj : j ∈ patientIndices family seen announced n) : j ≤ n := by
  have hlt : j < n + 1 := by
    simpa [Finset.mem_range] using patientIndices_subset_range family seen announced n hj
  omega

lemma patientIndices_chain
    (family : ℕ → Language) (seen announced : Finset ℕ) {n j k : ℕ}
    (hj : j ∈ patientIndices family seen announced n)
    (hk : k ∈ patientIndices family seen announced n) (hjk : j ≤ k) :
    family k ⊆ family j :=
  criticalIndices_chain family seen
    (patientIndices_subset_criticalIndices family seen announced n hj)
    (patientIndices_subset_criticalIndices family seen announced n hk) hjk

lemma criticalIndices_bound_mono
    (family : ℕ → Language) (seen : Finset ℕ) {a b : ℕ} (hab : a ≤ b) :
    criticalIndices family seen a ⊆ criticalIndices family seen b := by
  induction b, hab using Nat.le_induction with
  | base => exact Finset.Subset.rfl
  | succ b hab ih => exact ih.trans (criticalIndices_step_mono family seen b)

lemma criticalIndices_self_mem
    (family : ℕ → Language) (seen : Finset ℕ) (i : ℕ)
    (hi : Consistent family seen i)
    (hlower : ∀ j, j < i → Consistent family seen j → family i ⊆ family j) :
    i ∈ criticalIndices family seen i := by
  cases i with
  | zero => simp [criticalIndices, hi]
  | succ n =>
      have hinsert : Consistent family seen (n + 1) ∧
          ∀ j ∈ criticalIndices family seen n, family (n + 1) ⊆ family j := by
        refine ⟨hi, ?_⟩
        intro j hj
        apply hlower j
        · have := criticalIndices_mem_le family seen hj
          omega
        · exact criticalIndices_mem_consistent family seen hj
      rw [criticalIndices, if_pos hinsert]
      simp

lemma target_eventually_critical
    (family : ℕ → Language) {input : Stream} {i t bound : ℕ}
    (hp : GenLimit.Presents input (family i))
    (ht : criticalThreshold family input i ≤ t) (hib : i ≤ bound) :
    i ∈ criticalIndices family (inputSeenAt input t) bound := by
  apply criticalIndices_bound_mono family (inputSeenAt input t) hib
  apply criticalIndices_self_mem family (inputSeenAt input t) i
  · exact target_consistent family hp
  · intro j hj
    exact lower_consistent_contains_target family hp ht hj


lemma consistent_iff_target_subset
    (family : ℕ → Language) {input : Stream} {i t j : ℕ}
    (hp : GenLimit.Presents input (family i))
    (ht : criticalThreshold family input i ≤ t) (hji : j ≤ i) :
    Consistent family (inputSeenAt input t) j ↔ family i ⊆ family j := by
  constructor
  · intro hcons
    rcases hji.eq_or_lt with rfl | hlt
    · exact Set.Subset.rfl
    · exact lower_consistent_contains_target family hp ht hlt hcons
  · intro hsub x hx
    rcases Finset.mem_image.mp hx with ⟨s, -, rfl⟩
    exact hsub (presents_input_mem hp s)

lemma criticalIndices_congr
    (family : ℕ → Language) (seen₁ seen₂ : Finset ℕ) (n : ℕ)
    (hcons : ∀ j, j ≤ n →
      (Consistent family seen₁ j ↔ Consistent family seen₂ j)) :
    criticalIndices family seen₁ n = criticalIndices family seen₂ n := by
  induction n with
  | zero => simp [criticalIndices, hcons 0 (by omega)]
  | succ n ih =>
      have hprev : criticalIndices family seen₁ n =
          criticalIndices family seen₂ n :=
        ih fun j hj => hcons j (hj.trans (Nat.le_succ n))
      rw [criticalIndices, criticalIndices, hprev]
      simp only [hcons (n + 1) (by omega)]

lemma criticalIndices_stable
    (family : ℕ → Language) {input : Stream} {i a b n : ℕ}
    (hp : GenLimit.Presents input (family i))
    (ha : criticalThreshold family input i ≤ a)
    (hb : criticalThreshold family input i ≤ b) (hni : n ≤ i) :
    criticalIndices family (inputSeenAt input a) n =
      criticalIndices family (inputSeenAt input b) n := by
  apply criticalIndices_congr
  intro j hj
  rw [consistent_iff_target_subset family hp ha (hj.trans hni),
    consistent_iff_target_subset family hp hb (hj.trans hni)]

noncomputable def gateState
    (family : ℕ → Language) (input output : Stream) (i t : ℕ) :
    Finset (ℕ × ℕ) :=
  ((Finset.range (i + 1)).product (Finset.range (i + 1))).filter
    (fun q => ExhaustedBelow family (announcedAt input output t) q.1 q.2)

lemma gateState_mono
    (family : ℕ → Language) (input output : Stream) (i : ℕ) :
    Monotone (gateState family input output i) := by
  intro a b hab q hq
  simp only [gateState, Finset.mem_filter, Finset.mem_product] at hq ⊢
  exact ⟨hq.1, exhausted_mono_announced family
    (announcedAt_mono input output hab) hq.2⟩

lemma gateState_bound
    (family : ℕ → Language) (input output : Stream) (i t : ℕ) :
    gateState family input output i t ⊆
      (Finset.range (i + 1)).product (Finset.range (i + 1)) := by
  intro q hq
  exact (Finset.mem_filter.mp hq).1

lemma gateState_eventually_constant
    (family : ℕ → Language) (input output : Stream) (i : ℕ) :
    ∃ N, ∀ t, N ≤ t → gateState family input output i t =
      gateState family input output i N :=
  bounded_monotone_finset_eventually_constant
    (gateState family input output i)
    ((Finset.range (i + 1)).product (Finset.range (i + 1)))
    (gateState_mono family input output i)
    (gateState_bound family input output i)

lemma gate_iff_of_state_eq
    (family : ℕ → Language) (input output : Stream) {i a b p k : ℕ}
    (hstate : gateState family input output i a =
      gateState family input output i b)
    (hp : p ≤ i) (hk : k ≤ i) :
    ExhaustedBelow family (announcedAt input output a) p k ↔
      ExhaustedBelow family (announcedAt input output b) p k := by
  have hp' : p < i + 1 := by omega
  have hk' : k < i + 1 := by omega
  have := Finset.ext_iff.mp hstate (p, k)
  simpa [gateState, hp', hk'] using this

lemma patientIndices_congr
    (family : ℕ → Language) (seen₁ announced₁ seen₂ announced₂ : Finset ℕ)
    (n : ℕ)
    (hcrit : ∀ k, k ≤ n →
      criticalIndices family seen₁ k = criticalIndices family seen₂ k)
    (hgate : ∀ p k, p ≤ n → k ≤ n →
      (ExhaustedBelow family announced₁ p k ↔
        ExhaustedBelow family announced₂ p k)) :
    patientIndices family seen₁ announced₁ n =
      patientIndices family seen₂ announced₂ n := by
  induction n with
  | zero => simp [patientIndices, hcrit 0 (by omega)]
  | succ n ih =>
      have hprev := ih
        (fun k hk => hcrit k (hk.trans (Nat.le_succ n)))
        (fun p k hp hk => hgate p k
          (hp.trans (Nat.le_succ n)) (hk.trans (Nat.le_succ n)))
      rw [patientIndices, patientIndices, hprev,
        hcrit (n + 1) (by omega)]
      congr 1
      apply propext
      constructor
      · intro h
        refine ⟨h.1, fun hne => ?_⟩
        exact (hgate _ (n + 1)
          (patientIndices_mem_le family seen₂ announced₂
            (Finset.max'_mem _ hne) |>.trans (Nat.le_succ n))
          (by omega)).mp (h.2 hne)
      · intro h
        refine ⟨h.1, fun hne => ?_⟩
        exact (hgate _ (n + 1)
          (patientIndices_mem_le family seen₂ announced₂
            (Finset.max'_mem _ hne) |>.trans (Nat.le_succ n))
          (by omega)).mpr (h.2 hne)

lemma patientIndices_nonempty_of_critical
    (family : ℕ → Language) (seen announced : Finset ℕ) (n : ℕ)
    (hcrit : (criticalIndices family seen n).Nonempty) :
    (patientIndices family seen announced n).Nonempty := by
  induction n with
  | zero =>
      rcases hcrit with ⟨j, hj⟩
      have : j = 0 := by
        have := criticalIndices_mem_le family seen hj
        omega
      subst j
      simp [patientIndices, hj]
  | succ n ih =>
      by_cases hprev : (criticalIndices family seen n).Nonempty
      · exact (ih hprev).mono (patientIndices_step_mono family seen announced n)
      · have hpempty : patientIndices family seen announced n = ∅ := by
          apply Finset.eq_empty_iff_forall_not_mem.mpr
          intro j hj
          exact hprev ⟨j, patientIndices_subset_criticalIndices family seen announced n hj⟩
        have hnmem : n + 1 ∈ criticalIndices family seen (n + 1) := by
          by_cases hinsert : Consistent family seen (n + 1) ∧
              ∀ j ∈ criticalIndices family seen n,
                family (n + 1) ⊆ family j
          · rw [criticalIndices, if_pos hinsert]
            simp
          · rw [criticalIndices, if_neg hinsert] at hcrit
            exact (hprev hcrit).elim
        have hcond : n + 1 ∈ criticalIndices family seen (n + 1) ∧
            ∀ hne : (patientIndices family seen announced n).Nonempty,
              ExhaustedBelow family announced
                ((patientIndices family seen announced n).max' hne) (n + 1) := by
          refine ⟨hnmem, ?_⟩
          intro hne
          have : False := by simpa [hpempty] using hne
          contradiction
        rw [patientIndices, if_pos hcond]
        exact ⟨n + 1, by simp⟩


lemma patientIndices_bound_mono
    (family : ℕ → Language) (seen announced : Finset ℕ) {a b : ℕ} (hab : a ≤ b) :
    patientIndices family seen announced a ⊆
      patientIndices family seen announced b := by
  induction b, hab using Nat.le_induction with
  | base => exact Finset.Subset.rfl
  | succ b hab ih => exact ih.trans (patientIndices_step_mono family seen announced b)

lemma patientIndices_mem_iff_of_le
    (family : ℕ → Language) (seen announced : Finset ℕ)
    {a b j : ℕ} (hab : a ≤ b) (hj : j ≤ a) :
    j ∈ patientIndices family seen announced b ↔
      j ∈ patientIndices family seen announced a := by
  induction b, hab using Nat.le_induction with
  | base => exact Iff.rfl
  | succ b hab ih =>
      by_cases h : b + 1 ∈ criticalIndices family seen (b + 1) ∧
          ∀ hne : (patientIndices family seen announced b).Nonempty,
            ExhaustedBelow family announced
              ((patientIndices family seen announced b).max' hne) (b + 1)
      · simp only [patientIndices, if_pos h, Finset.mem_insert]
        rw [ih]
        constructor
        · intro hj'
          rcases hj' with rfl | hj'
          · omega
          · exact hj'
        · exact Or.inr
      · simpa only [patientIndices, if_neg h] using ih

lemma patientIndices_eventually_constant_below
    (family : ℕ → Language) {input output : Stream} {i : ℕ}
    (hp : GenLimit.Presents input (family i)) :
    ∃ N, ∀ t, N ≤ t →
      patientIndices family (inputSeenAt input t) (announcedAt input output t) i =
        patientIndices family (inputSeenAt input N) (announcedAt input output N) i := by
  rcases gateState_eventually_constant family input output i with ⟨G, hG⟩
  let N := max G (criticalThreshold family input i)
  refine ⟨N, fun t ht => ?_⟩
  apply patientIndices_congr
  · intro k hk
    apply criticalIndices_stable family hp
    · exact (le_max_right _ _).trans ht
    · exact le_max_right _ _
    · exact hk
  · intro p k hp' hk'
    apply gate_iff_of_state_eq family input output
    · calc
        gateState family input output i t = gateState family input output i G :=
          hG t ((le_max_left _ _).trans ht)
        _ = gateState family input output i N :=
          (hG N (le_max_left _ _)).symm
    · exact hp'
    · exact hk'


noncomputable def trajectory (gen : OnlineGenerator) (input : Stream) (t : ℕ) : ℕ :=
  gen t (fun i => input i) (fun i => trajectory gen input i)
termination_by t
decreasing_by omega

lemma trajectory_follows (gen : OnlineGenerator) (input : Stream) :
    Follows gen input (trajectory gen input) := by
  intro t
  rw [trajectory]


lemma focusIndex_mem
    (family : ℕ → Language) (seen announced : Finset ℕ) (bound : ℕ)
    (h : (patientIndices family seen announced bound).Nonempty) :
    focusIndex family seen announced bound ∈
      patientIndices family seen announced bound := by
  simp only [focusIndex, dif_pos h]
  exact Finset.max'_mem _ h

lemma focusLanguage_infinite
    (family : ℕ → Language) (hfamily : ∀ i, (family i).Infinite)
    (seen announced : Finset ℕ) (bound : ℕ) :
    (focusLanguage family seen announced bound).Infinite := by
  by_cases h : (patientIndices family seen announced bound).Nonempty
  · simp only [focusLanguage, if_pos h]
    exact hfamily _
  · simp only [focusLanguage, if_neg h]
    exact Set.infinite_univ

lemma patientGenerator_mem_and_fresh
    (family : ℕ → Language) (hfamily : ∀ i, (family i).Infinite)
    (t : ℕ) (input : Fin (t + 1) → ℕ) (output : Fin t → ℕ) :
    let inputSeen := Finset.univ.image input
    let announced := inputSeen ∪ Finset.univ.image output
    let z := patientGenerator family t input output
    z ∈ focusLanguage family inputSeen announced t ∧ z ∉ announced := by
  classical
  dsimp [patientGenerator]
  let inputSeen := Finset.univ.image input
  let announced := inputSeen ∪ Finset.univ.image output
  have hfresh := infinite_has_fresh
    (focusLanguage_infinite family hfamily inputSeen announced t) announced
  exact ⟨leastFresh_mem hfresh, leastFresh_not_mem hfresh⟩

lemma trajectory_avoids_input
    (family : ℕ → Language) (hfamily : ∀ i, (family i).Infinite)
    (input : Stream) (t s : ℕ) (hst : s ≤ t) :
    trajectory (patientGenerator family) input t ≠ input s := by
  classical
  have hfresh := (patientGenerator_mem_and_fresh family hfamily t
    (fun i => input i) (fun i => trajectory (patientGenerator family) input i)).2
  intro heq
  rw [trajectory] at heq
  apply hfresh
  apply Finset.mem_union_left
  apply Finset.mem_image.mpr
  exact ⟨⟨s, by omega⟩, Finset.mem_univ _, heq.symm⟩

lemma trajectory_no_repeat
    (family : ℕ → Language) (hfamily : ∀ i, (family i).Infinite)
    (input : Stream) (t s : ℕ) (hst : s < t) :
    trajectory (patientGenerator family) input s ≠
      trajectory (patientGenerator family) input t := by
  classical
  have hfresh := (patientGenerator_mem_and_fresh family hfamily t
    (fun i => input i) (fun i => trajectory (patientGenerator family) input i)).2
  intro heq
  apply hfresh
  apply Finset.mem_union_right
  apply Finset.mem_image.mpr
  refine ⟨⟨s, hst⟩, Finset.mem_univ _, ?_⟩
  calc
    trajectory (patientGenerator family) input s =
        trajectory (patientGenerator family) input t := heq
    _ = patientGenerator family t (fun i => input i)
        (fun i => trajectory (patientGenerator family) input i) := by rw [trajectory]

lemma trajectory_mem_focus
    (family : ℕ → Language) (hfamily : ∀ i, (family i).Infinite)
    (input : Stream) (t : ℕ) :
    trajectory (patientGenerator family) input t ∈
      focusLanguage family
        (Finset.univ.image (fun i : Fin (t + 1) => input i))
        ((Finset.univ.image (fun i : Fin (t + 1) => input i)) ∪
          Finset.univ.image
            (fun i : Fin t => trajectory (patientGenerator family) input i)) t := by
  rw [trajectory]
  exact (patientGenerator_mem_and_fresh family hfamily t
    (fun i => input i) (fun i => trajectory (patientGenerator family) input i)).1

end

end Case025Proof

theorem stage3_result : Stage3Case025.MainClaim := by
  sorry
