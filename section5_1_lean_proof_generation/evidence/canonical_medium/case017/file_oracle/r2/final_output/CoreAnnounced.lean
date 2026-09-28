import Stage3Model
import GenLimit.Paper39_DenseGeneration.Abstract.PartialDensity

open Set Filter
open GenLimit.PatientScope
open scoped Topology

namespace Case017Proof

noncomputable def compatibleCore {m t : ℕ}
    (family : Fin m → Set ℕ) (xs : Fin t → ℕ) : Set ℕ :=
  {z | ∀ j, (∀ i, xs i ∈ family j) → z ∈ family j}

noncomputable def seen {t : ℕ} (xs : Fin (t + 1) → ℕ)
    (ys : Fin t → ℕ) : Finset ℕ :=
  GenLimit.Generic.sequenceSample xs ∪ GenLimit.Generic.sequenceSample ys

noncomputable def leastFresh (S : Set ℕ) (F : Finset ℕ)
    (hS : S.Infinite) : ℕ := by
  classical
  exact Nat.find (hS.exists_notMem_finset F)

lemma leastFresh_spec (S : Set ℕ) (F : Finset ℕ) (hS : S.Infinite) :
    leastFresh S F hS ∈ S ∧ leastFresh S F hS ∉ F := by
  classical
  exact Nat.find_spec (hS.exists_notMem_finset F)

lemma leastFresh_le (S : Set ℕ) (F : Finset ℕ) (hS : S.Infinite)
    {z : ℕ} (hzS : z ∈ S) (hzF : z ∉ F) :
    leastFresh S F hS ≤ z := by
  classical
  exact Nat.find_min' (hS.exists_notMem_finset F) ⟨hzS, hzF⟩

noncomputable def familyGenerator {m : ℕ} (family : Fin m → Set ℕ) :
    Stage3Case017.OnlineGenerator :=
  fun t xs ys => by
    classical
    let C := compatibleCore family xs
    let F := seen xs ys
    exact if hC : C.Infinite then leastFresh C F hC
      else leastFresh Set.univ F Set.infinite_univ

noncomputable def trajectory (gen : Stage3Case017.OnlineGenerator)
    (input : ℕ → ℕ) : ℕ → ℕ :=
  Nat.lt_wfRel.wf.fix fun t previous =>
    gen t (fun i => input i) (fun i => previous i i.isLt)

lemma trajectory_eq (gen : Stage3Case017.OnlineGenerator)
    (input : ℕ → ℕ) (t : ℕ) :
    trajectory gen input t =
      gen t (fun i => input i) (fun i => trajectory gen input i) := by
  rw [trajectory, WellFounded.fix_eq]

lemma trajectory_follows (gen : Stage3Case017.OnlineGenerator)
    (input : ℕ → ℕ) :
    Stage3Case017.Follows gen input (trajectory gen input) := by
  exact trajectory_eq gen input

noncomputable def familyOutput {m : ℕ} (family : Fin m → Set ℕ)
    (input : ℕ → ℕ) : ℕ → ℕ :=
  trajectory (familyGenerator family) input

lemma familyOutput_eq {m : ℕ} (family : Fin m → Set ℕ)
    (input : ℕ → ℕ) (t : ℕ) :
    familyOutput family input t = familyGenerator family t
      (fun i => input i) (fun i => familyOutput family input i) := by
  exact trajectory_eq (familyGenerator family) input t


lemma mem_seen_input {t : ℕ} {xs : Fin (t + 1) → ℕ} {ys : Fin t → ℕ}
    {z : ℕ} (i : Fin (t + 1)) (hiz : xs i = z) : z ∈ seen xs ys := by
  apply Finset.mem_union_left
  rw [GenLimit.Generic.mem_sequenceSample_iff]
  exact ⟨i, hiz⟩

lemma mem_seen_output {t : ℕ} {xs : Fin (t + 1) → ℕ} {ys : Fin t → ℕ}
    {z : ℕ} (i : Fin t) (hiz : ys i = z) : z ∈ seen xs ys := by
  apply Finset.mem_union_right
  rw [GenLimit.Generic.mem_sequenceSample_iff]
  exact ⟨i, hiz⟩

lemma familyGenerator_not_seen {m t : ℕ} (family : Fin m → Set ℕ)
    (xs : Fin (t + 1) → ℕ) (ys : Fin t → ℕ) :
    familyGenerator family t xs ys ∉ seen xs ys := by
  classical
  unfold familyGenerator
  dsimp only
  split <;> rename_i h
  · exact (leastFresh_spec _ _ h).2
  · exact (leastFresh_spec _ _ Set.infinite_univ).2

lemma familyGenerator_mem_core_of_infinite {m t : ℕ}
    (family : Fin m → Set ℕ) (xs : Fin (t + 1) → ℕ) (ys : Fin t → ℕ)
    (hcore : (compatibleCore family xs).Infinite) :
    familyGenerator family t xs ys ∈ compatibleCore family xs := by
  classical
  unfold familyGenerator
  dsimp only
  rw [dif_pos hcore]
  exact (leastFresh_spec _ _ hcore).1

lemma familyGenerator_le_of_available {m t : ℕ}
    (family : Fin m → Set ℕ) (xs : Fin (t + 1) → ℕ) (ys : Fin t → ℕ)
    (hcore : (compatibleCore family xs).Infinite) {z : ℕ}
    (hzcore : z ∈ compatibleCore family xs) (hzfresh : z ∉ seen xs ys) :
    familyGenerator family t xs ys ≤ z := by
  classical
  unfold familyGenerator
  dsimp only
  rw [dif_pos hcore]
  exact leastFresh_le _ _ hcore hzcore hzfresh

lemma compatible_eventually {m : ℕ} (family : Fin m → Set ℕ)
    (input : ℕ → ℕ) (j : Fin m) :
    ∃ T, ∀ t, T ≤ t →
      ((∀ i : Fin (t + 1), input i ∈ family j) ↔
        GenLimit.Generic.StreamIn input (family j)) := by
  classical
  by_cases hgood : GenLimit.Generic.StreamIn input (family j)
  · exact ⟨0, fun _ _ => ⟨fun _ => hgood, fun _ i => hgood ⟨i, rfl⟩⟩⟩
  · obtain ⟨z, ⟨q, rfl⟩, hz⟩ := Set.not_subset.mp hgood
    refine ⟨q, ?_⟩
    intro t hqt
    constructor
    · intro hpref
      exact False.elim (hz (hpref ⟨q, by omega⟩))
    · intro hstream
      exact False.elim (hgood hstream)

lemma cores_eventually_equal {m : ℕ} (family : Fin m → Set ℕ)
    (input : ℕ → ℕ) :
    ∃ T, ∀ t, T ≤ t →
      compatibleCore family (fun i : Fin (t + 1) => input i) =
        Stage3Case017.informationCore family input := by
  classical
  choose threshold hthreshold using fun j => compatible_eventually family input j
  let T := ∑ j : Fin m, threshold j
  refine ⟨T, ?_⟩
  intro t hT
  ext z
  simp only [compatibleCore, Stage3Case017.informationCore, Set.mem_setOf_eq]
  constructor
  · intro hz j hj
    apply hz j
    exact (hthreshold j t (le_trans (Finset.single_le_sum
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)) hT)).2 hj
  · intro hz j hj
    apply hz j
    exact (hthreshold j t (le_trans (Finset.single_le_sum
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)) hT)).1 hj

lemma informationCore_subset {m : ℕ} {family : Fin m → Set ℕ}
    {input : ℕ → ℕ} {j : Fin m}
    (hj : GenLimit.Generic.StreamIn input (family j)) :
    Stage3Case017.informationCore family input ⊆ family j := by
  intro z hz
  exact hz j hj

lemma trajectory_novel_after_stabilization {m : ℕ}
    (family : Fin m → Set ℕ) (input : ℕ → ℕ)
    (hcore : (Stage3Case017.informationCore family input).Infinite) :
    ∃ T, ∀ t, T ≤ t →
      trajectory (familyGenerator family) input t ∈
          Stage3Case017.informationCore family input ∧
      trajectory (familyGenerator family) input t ∉
          GenLimit.Generic.sample input (t + 1) ∧
      ∀ s, s < t →
        trajectory (familyGenerator family) input s ≠
          trajectory (familyGenerator family) input t := by
  obtain ⟨T, hT⟩ := cores_eventually_equal family input
  refine ⟨T, ?_⟩
  intro t ht
  have heq := hT t ht
  have hcurrent :
      (compatibleCore family (fun i : Fin (t + 1) => input i)).Infinite := by
    rw [heq]
    exact hcore
  have houtEq := trajectory_eq (familyGenerator family) input t
  have hgenmem : familyGenerator family t
      (fun i : Fin (t + 1) => input i)
      (fun i : Fin t => trajectory (familyGenerator family) input i) ∈
      compatibleCore family (fun i : Fin (t + 1) => input i) :=
    familyGenerator_mem_core_of_infinite family _ _ hcurrent
  have hmem : trajectory (familyGenerator family) input t ∈
      compatibleCore family (fun i : Fin (t + 1) => input i) :=
    houtEq.symm ▸ hgenmem
  refine ⟨heq ▸ hmem, ?_, ?_⟩
  · intro hsamp
    rw [GenLimit.Generic.mem_sample_iff] at hsamp
    obtain ⟨s, hs, hval⟩ := hsamp
    have hi : s < t + 1 := hs
    have hseen := mem_seen_input
      (xs := fun i : Fin (t + 1) => input i)
      (ys := fun i : Fin t => trajectory (familyGenerator family) input i)
      (i := ⟨s, hi⟩) hval
    have hnot := familyGenerator_not_seen family
      (fun i : Fin (t + 1) => input i)
      (fun i : Fin t => trajectory (familyGenerator family) input i)
    exact hnot (houtEq ▸ hseen)
  · intro s hst hequal
    have hseen := mem_seen_output
      (xs := fun i : Fin (t + 1) => input i)
      (ys := fun i : Fin t => trajectory (familyGenerator family) input i)
      (i := ⟨s, hst⟩) hequal
    have hnot := familyGenerator_not_seen family
      (fun i : Fin (t + 1) => input i)
      (fun i : Fin t => trajectory (familyGenerator family) input i)
    exact hnot (houtEq ▸ hseen)


lemma core_point_announced {m : ℕ} (family : Fin m → Set ℕ)
    (input : ℕ → ℕ) (hcore : (Stage3Case017.informationCore family input).Infinite)
    (z : ℕ) (hz : z ∈ Stage3Case017.informationCore family input) :
    z ∈ Set.range input ∪ Set.range (familyOutput family input) := by
  classical
  induction z using Nat.strong_induction_on with
  | h z ih =>
      by_contra hnot
      have hlower : ∀ y : Fin z, ∃ q : ℕ,
          (y : ℕ) ∈ Stage3Case017.informationCore family input →
            input q = (y : ℕ) ∨ familyOutput family input q = (y : ℕ) := by
        intro y
        by_cases hy : (y : ℕ) ∈ Stage3Case017.informationCore family input
        · have ha := ih y y.isLt hy
          rcases ha with ha | ha
          · obtain ⟨q, hq⟩ := ha
            exact ⟨q, fun _ => Or.inl hq⟩
          · obtain ⟨q, hq⟩ := ha
            exact ⟨q, fun _ => Or.inr hq⟩
        · exact ⟨0, fun h => False.elim (hy h)⟩
      choose q hq using hlower
      obtain ⟨T, hT⟩ := cores_eventually_equal family input
      let Q := ∑ y : Fin z, (q y + 1)
      let B := T + Q
      have hTB : T ≤ B := Nat.le_add_right _ _
      have heq := hT B hTB
      have hcurrent :
          (compatibleCore family (fun i : Fin (B + 1) => input i)).Infinite := by
        rw [heq]
        exact hcore
      have hzcurrent : z ∈ compatibleCore family
          (fun i : Fin (B + 1) => input i) := by
        rw [heq]
        exact hz
      have hzfresh : z ∉ seen
          (fun i : Fin (B + 1) => input i)
          (fun i : Fin B => output i) := by
        intro hseen
        rcases Finset.mem_union.mp hseen with hin | hout
        · rw [GenLimit.Generic.mem_sequenceSample_iff] at hin
          obtain ⟨i, hi⟩ := hin
          exact hnot (Set.mem_union_left _ ⟨i, hi⟩)
        · rw [GenLimit.Generic.mem_sequenceSample_iff] at hout
          obtain ⟨i, hi⟩ := hout
          exact hnot (Set.mem_union_right _ ⟨i, hi⟩)
      have houtEq := familyOutput_eq family input B
      have hgenle : familyGenerator family B
          (fun i : Fin (B + 1) => input i)
          (fun i : Fin B => familyOutput family input i) ≤ z :=
        familyGenerator_le_of_available family _ _ hcurrent hzcurrent hzfresh
      have hle : familyOutput family input B ≤ z := by
        change familyOutput family input B ≤ z
        exact houtEq.symm ▸ hgenle
      have houtcore : familyOutput family input B ∈ Stage3Case017.informationCore family input := by
        change familyOutput family input B ∈ _
        have hmem : familyGenerator family B
            (fun i : Fin (B + 1) => input i)
            (fun i : Fin B => familyOutput family input i) ∈
            compatibleCore family (fun i : Fin (B + 1) => input i) :=
          familyGenerator_mem_core_of_infinite family _ _ hcurrent
        exact houtEq.symm ▸ (heq ▸ hmem)
      have hnotseen : familyOutput family input B ∉ seen
          (fun i : Fin (B + 1) => input i) (fun i : Fin B => output i) := by
        change familyOutput family input B ∉ _
        have hnotgen := familyGenerator_not_seen family
          (fun i : Fin (B + 1) => input i)
          (fun i : Fin B => familyOutput family input i)
        exact houtEq.symm ▸ hnotgen
      have hnotlt : ¬ familyOutput family input B < z := by
        intro hlt
        let y : Fin z := ⟨familyOutput family input B, hlt⟩
        have htime := hq y houtcore
        have hqQ : q y + 1 ≤ Q := by
          exact Finset.single_le_sum (fun _ _ => Nat.zero_le _)
            (Finset.mem_univ y)
        have hqB : q y < B := by
          dsimp [B]
          omega
        apply hnotseen
        rcases htime with hin | hout
        · exact mem_seen_input (i := ⟨q y, by omega⟩) hin
        · exact mem_seen_output (i := ⟨q y, hqB⟩) hout
      have heqz : familyOutput family input B = z :=
        Nat.le_antisymm hle (Nat.le_of_not_gt hnotlt)
      apply hnot
      exact Set.mem_union_right _ ⟨B, heqz⟩

end Case017Proof
