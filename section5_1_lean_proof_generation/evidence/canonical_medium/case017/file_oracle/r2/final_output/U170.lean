import Stage3Model
import GenLimit.Paper39_DenseGeneration.Abstract.PartialDensity

open Set Filter
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
  have hmem : trajectory (familyGenerator family) input t ∈
      compatibleCore family (fun i : Fin (t + 1) => input i) := by
    rw [trajectory_eq]
    exact familyGenerator_mem_core_of_infinite family _ _ hcurrent
end Case017Proof
