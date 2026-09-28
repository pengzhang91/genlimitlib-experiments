import Stage3Model
import Mathlib.Data.Nat.Log

open Set
open Stage3Case025

namespace Case025

noncomputable def finiteValues {n : ℕ} (xs : Fin n → ℕ) : Finset ℕ :=
  Finset.univ.image xs

noncomputable def scope (family : ℕ → Language) (seen : Finset ℕ) : ℕ → Language
  | 0 => Set.univ
  | j + 1 =>
      by
        classical
        exact if (↑seen : Set ℕ) ⊆ family j ∧ family j ⊆ scope family seen j then
          family j
        else
          scope family seen j

lemma scope_infinite (family : ℕ → Language) (hfamily : ∀ i, (family i).Infinite)
    (seen : Finset ℕ) : ∀ j, (scope family seen j).Infinite := by
  intro j
  induction j with
  | zero => simpa [scope] using (Set.infinite_univ : (Set.univ : Set ℕ).Infinite)
  | succ j ih =>
      simp only [scope]
      split <;> simp_all

lemma scope_succ_subset (family : ℕ → Language) (seen : Finset ℕ) (j : ℕ) :
    scope family seen (j + 1) ⊆ scope family seen j := by
  simp only [scope]
  split <;> simp_all

noncomputable def freshIn (S : Language) (hS : S.Infinite) (used : Finset ℕ) : ℕ := by
  classical
  exact Nat.find (hS.exists_notMem_finset used)

lemma freshIn_spec (S : Language) (hS : S.Infinite) (used : Finset ℕ) :
    freshIn S hS used ∈ S ∧ freshIn S hS used ∉ used := by
  classical
  exact Nat.find_spec (hS.exists_notMem_finset used)

lemma freshIn_mem (S : Language) (hS : S.Infinite) (used : Finset ℕ) :
    freshIn S hS used ∈ S := (freshIn_spec S hS used).1

lemma freshIn_not_mem (S : Language) (hS : S.Infinite) (used : Finset ℕ) :
    freshIn S hS used ∉ used := (freshIn_spec S hS used).2

lemma freshIn_le (S : Language) (hS : S.Infinite) (used : Finset ℕ)
    {x : ℕ} (hxS : x ∈ S) (hxused : x ∉ used) : freshIn S hS used ≤ x := by
  classical
  exact Nat.find_min' (hS.exists_notMem_finset used) ⟨hxS, hxused⟩

noncomputable def delayedDepth (t : ℕ) : ℕ := Nat.log2 (t + 1)

noncomputable def patientGenerator
    (family : ℕ → Language) (hfamily : ∀ i, (family i).Infinite) : OnlineGenerator :=
  fun t input previous =>
    let seen := finiteValues input
    let used := seen ∪ finiteValues previous
    let current := scope family seen (delayedDepth t)
    freshIn current (scope_infinite family hfamily seen (delayedDepth t)) used

lemma patientGenerator_mem_scope
    (family : ℕ → Language) (hfamily : ∀ i, (family i).Infinite)
    (t : ℕ) (input : Fin (t + 1) → ℕ) (previous : Fin t → ℕ) :
    patientGenerator family hfamily t input previous ∈
      scope family (finiteValues input) (delayedDepth t) := by
  simp only [patientGenerator]
  exact freshIn_mem _ _ _

lemma patientGenerator_not_input
    (family : ℕ → Language) (hfamily : ∀ i, (family i).Infinite)
    (t : ℕ) (input : Fin (t + 1) → ℕ) (previous : Fin t → ℕ) :
    patientGenerator family hfamily t input previous ∉ finiteValues input := by
  have h := freshIn_not_mem
    (scope family (finiteValues input) (delayedDepth t))
    (scope_infinite family hfamily (finiteValues input) (delayedDepth t))
    (finiteValues input ∪ finiteValues previous)
  simpa only [patientGenerator] using fun hm => h (Finset.mem_union_left _ hm)

lemma patientGenerator_not_previous
    (family : ℕ → Language) (hfamily : ∀ i, (family i).Infinite)
    (t : ℕ) (input : Fin (t + 1) → ℕ) (previous : Fin t → ℕ) :
    patientGenerator family hfamily t input previous ∉ finiteValues previous := by
  have h := freshIn_not_mem
    (scope family (finiteValues input) (delayedDepth t))
    (scope_infinite family hfamily (finiteValues input) (delayedDepth t))
    (finiteValues input ∪ finiteValues previous)
  simpa only [patientGenerator] using fun hm => h (Finset.mem_union_right _ hm)

noncomputable def trajectory (gen : OnlineGenerator) (input : Stream) (t : ℕ) : ℕ :=
  gen t (fun i => input i) (fun i => trajectory gen input i)
termination_by t
decreasing_by exact i.isLt

lemma trajectory_follows (gen : OnlineGenerator) (input : Stream) :
    Follows gen input (trajectory gen input) := by
  intro t
  exact trajectory.eq_def gen input t

lemma mem_finiteValues_iff {n : ℕ} (xs : Fin n → ℕ) (x : ℕ) :
    x ∈ finiteValues xs ↔ ∃ i, xs i = x := by
  simp [finiteValues]

lemma trajectory_eq_generator
    (gen : OnlineGenerator) (input : Stream) (t : ℕ) :
    trajectory gen input t = gen t (fun i => input i) (fun i => trajectory gen input i) :=
  trajectory_follows gen input t

lemma trajectory_fresh
    (family : ℕ → Language) (hfamily : ∀ i, (family i).Infinite)
    (input : Stream) (t : ℕ) :
    trajectory (patientGenerator family hfamily) input t ∉ GenLimit.sample input (t + 1) := by
  rw [trajectory_eq_generator]
  have h := patientGenerator_not_input family hfamily t
    (fun i => input i)
    (fun i => trajectory (patientGenerator family hfamily) input i)
  intro hsample
  apply h
  rw [mem_finiteValues_iff]
  rw [GenLimit.sample, Finset.mem_image] at hsample
  rcases hsample with ⟨a, ha, hea⟩
  exact ⟨⟨a, by simpa using ha⟩, hea⟩

lemma trajectory_ne_of_lt
    (family : ℕ → Language) (hfamily : ∀ i, (family i).Infinite)
    (input : Stream) {a b : ℕ} (hab : a < b) :
    trajectory (patientGenerator family hfamily) input a ≠
      trajectory (patientGenerator family hfamily) input b := by
  have hnot := patientGenerator_not_previous family hfamily b
    (fun i => input i)
    (fun i => trajectory (patientGenerator family hfamily) input i)
  intro heq
  apply hnot
  rw [mem_finiteValues_iff]
  refine ⟨⟨a, hab⟩, ?_⟩
  calc
    trajectory (patientGenerator family hfamily) input a =
        trajectory (patientGenerator family hfamily) input b := heq
    _ = patientGenerator family hfamily b (fun i => input i)
        (fun i => trajectory (patientGenerator family hfamily) input i) :=
      trajectory_eq_generator _ _ _

lemma trajectory_injective
    (family : ℕ → Language) (hfamily : ∀ i, (family i).Infinite)
    (input : Stream) : Function.Injective (trajectory (patientGenerator family hfamily) input) := by
  intro a b hab
  rcases lt_trichotomy a b with hablt | rfl | hbalt
  · exact (trajectory_ne_of_lt family hfamily input hablt hab).elim
  · rfl
  · exact (trajectory_ne_of_lt family hfamily input hbalt hab.symm).elim

end Case025

namespace Case025

lemma finiteValues_subset_of_range_subset {n : ℕ} (xs : Fin n → ℕ)
    (input : Stream) (hxs : ∀ i, xs i = input i) (K : Language)
    (hrange : Set.range input ⊆ K) : (↑(finiteValues xs) : Set ℕ) ⊆ K := by
  intro x hx
  change x ∈ finiteValues xs at hx
  rw [mem_finiteValues_iff] at hx
  rcases hx with ⟨i, rfl⟩
  rw [hxs]
  exact hrange ⟨i, rfl⟩

lemma input_mem_seen (input : Stream) {r t : ℕ} (hrt : r ≤ t) :
    input r ∈ finiteValues (fun i : Fin (t + 1) => input i) := by
  rw [mem_finiteValues_iff]
  exact ⟨⟨r, by omega⟩, rfl⟩

lemma scope_antitone_depth (family : ℕ → Language) (seen : Finset ℕ)
    {a b : ℕ} (hab : a ≤ b) : scope family seen b ⊆ scope family seen a := by
  induction b, hab using Nat.le_induction with
  | base => exact fun _ hx => hx
  | succ b hab ih => exact fun x hx => ih (scope_succ_subset family seen b hx)

lemma target_subset_scope_eventually
    (family : ℕ → Language) (input : Stream) (K : Language)
    (hpresents : GenLimit.Presents input K) :
    ∀ j, ∃ T, ∀ t, T ≤ t →
      K ⊆ scope family (finiteValues (fun i : Fin (t + 1) => input i)) j := by
  intro j
  induction j with
  | zero =>
      exact ⟨0, by simp [scope]⟩
  | succ j ih =>
      rcases ih with ⟨T, hT⟩
      by_cases hsub : K ⊆ family j
      · refine ⟨T, ?_⟩
        intro t ht x hx
        simp only [scope]
        split
        · exact hsub hx
        · exact hT t ht hx
      · rcases Set.not_subset.mp hsub with ⟨x, hxK, hxnot⟩
        rw [GenLimit.Presents] at hpresents
        have hxrange : x ∈ Set.range input := hpresents.symm ▸ hxK
        rcases hxrange with ⟨r, hr⟩
        refine ⟨max T r, ?_⟩
        intro t ht
        have hTt : T ≤ t := le_trans (le_max_left _ _) ht
        have hrt : r ≤ t := le_trans (le_max_right _ _) ht
        simp only [scope]
        split
        · rename_i hselect
          exfalso
          exact hxnot (hselect.1 (by simpa [hr] using input_mem_seen input hrt))
        · exact hT t hTt

lemma scope_eq_target_eventually
    (family : ℕ → Language) (input : Stream) (i : ℕ)
    (hpresents : GenLimit.Presents input (family i)) :
    ∃ T, ∀ t, T ≤ t →
      scope family (finiteValues (fun k : Fin (t + 1) => input k)) (i + 1) = family i := by
  rcases target_subset_scope_eventually family input (family i) hpresents i with ⟨T, hT⟩
  refine ⟨T, ?_⟩
  intro t ht
  simp only [scope]
  rw [if_pos]
  constructor
  · rw [← hpresents]
    exact finiteValues_subset_of_range_subset _ input (fun _ => rfl) _ (by rfl)
  · exact hT t ht

lemma delayedDepth_eventually_ge (j : ℕ) :
    ∃ T, ∀ t, T ≤ t → j ≤ delayedDepth t := by
  refine ⟨2 ^ j, ?_⟩
  intro t ht
  rw [delayedDepth, Nat.le_log2 (by omega)]
  omega

lemma trajectory_eventually_target
    (family : ℕ → Language) (hfamily : ∀ i, (family i).Infinite)
    (i : ℕ) (input : Stream) (hpresents : GenLimit.Presents input (family i)) :
    ∃ T, ∀ t, T ≤ t →
      trajectory (patientGenerator family hfamily) input t ∈ family i := by
  rcases scope_eq_target_eventually family input i hpresents with ⟨T₁, hT₁⟩
  rcases delayedDepth_eventually_ge (i + 1) with ⟨T₂, hT₂⟩
  refine ⟨max T₁ T₂, ?_⟩
  intro t ht
  rw [trajectory_eq_generator]
  have hmem := patientGenerator_mem_scope family hfamily t
    (fun k => input k) (fun k => trajectory (patientGenerator family hfamily) input k)
  have hdepth := scope_antitone_depth family
    (finiteValues (fun k : Fin (t + 1) => input k)) (hT₂ t (le_trans (le_max_right _ _) ht))
  have heq := hT₁ t (le_trans (le_max_left _ _) ht)
  rw [heq] at hdepth
  exact hdepth hmem

lemma patient_novel_generates
    (family : ℕ → Language) (hfamily : ∀ i, (family i).Infinite)
    (i : ℕ) (input : Stream) (hpresents : GenLimit.Presents input (family i)) :
    GenLimit.NovelGeneratesInLimit input
      (trajectory (patientGenerator family hfamily) input) (family i) := by
  rcases trajectory_eventually_target family hfamily i input hpresents with ⟨T, hT⟩
  refine ⟨T, ?_⟩
  intro t ht
  refine ⟨hT t ht, trajectory_fresh family hfamily input t, ?_⟩
  intro s hst
  exact trajectory_ne_of_lt family hfamily input hst

end Case025
