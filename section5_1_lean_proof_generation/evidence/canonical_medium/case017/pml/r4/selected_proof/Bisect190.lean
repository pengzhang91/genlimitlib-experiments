import Stage3Model
import GenLimit.Paper39_DenseGeneration.Abstract.TargetDensity

open Set Filter

namespace Stage3Case017Proof

open GenLimit
open GenLimit.Generic
open GenLimit.PatientScope
open Stage3Case017

noncomputable def historySet {n : ℕ} (xs : Fin n → ℕ) : Finset ℕ :=
  sequenceSample xs

def roundCore {m t : ℕ} (family : Fin m → Set ℕ)
    (xs : Fin (t + 1) → ℕ) : Set ℕ :=
  {z | ∀ j, (∀ i, xs i ∈ family j) → z ∈ family j}

theorem exists_fresh (C : Set ℕ) (hC : C.Infinite) (seen : Finset ℕ) :
    ∃ z, z ∈ C ∧ z ∉ seen := by
  have hnonempty := (hC.diff seen.finite_toSet).nonempty
  simpa only [Set.mem_diff, Finset.mem_coe] using hnonempty

noncomputable def leastFresh (C : Set ℕ) (hC : C.Infinite)
    (seen : Finset ℕ) : ℕ := by
  classical
  exact Nat.find (exists_fresh C hC seen)

theorem leastFresh_mem (C : Set ℕ) (hC : C.Infinite) (seen : Finset ℕ) :
    leastFresh C hC seen ∈ C := by
  classical
  exact (Nat.find_spec (exists_fresh C hC seen)).1

theorem leastFresh_not_mem (C : Set ℕ) (hC : C.Infinite) (seen : Finset ℕ) :
    leastFresh C hC seen ∉ seen := by
  classical
  exact (Nat.find_spec (exists_fresh C hC seen)).2

theorem leastFresh_le (C : Set ℕ) (hC : C.Infinite) (seen : Finset ℕ)
    {z : ℕ} (hzC : z ∈ C) (hzseen : z ∉ seen) :
    leastFresh C hC seen ≤ z := by
  classical
  exact Nat.find_min' (exists_fresh C hC seen) ⟨hzC, hzseen⟩

noncomputable def generator {m : ℕ} (family : Fin m → Set ℕ) : OnlineGenerator := by
  classical
  exact fun t xs ys =>
    let C := roundCore family xs
    let seen := historySet xs ∪ historySet ys
    if hC : C.Infinite then leastFresh C hC seen
    else leastFresh Set.univ Set.infinite_univ seen

theorem generator_not_input {m t : ℕ} (family : Fin m → Set ℕ)
    (xs : Fin (t + 1) → ℕ) (ys : Fin t → ℕ) :
    generator family t xs ys ∉ historySet xs := by
  classical
  unfold generator
  dsimp only
  split_ifs with hC
  · exact fun h => leastFresh_not_mem _ hC _ (Finset.mem_union_left _ h)
  · exact fun h => leastFresh_not_mem _ Set.infinite_univ _ (Finset.mem_union_left _ h)

theorem generator_not_output {m t : ℕ} (family : Fin m → Set ℕ)
    (xs : Fin (t + 1) → ℕ) (ys : Fin t → ℕ) :
    generator family t xs ys ∉ historySet ys := by
  classical
  unfold generator
  dsimp only
  split_ifs with hC
  · exact fun h => leastFresh_not_mem _ hC _ (Finset.mem_union_right _ h)
  · exact fun h => leastFresh_not_mem _ Set.infinite_univ _ (Finset.mem_union_right _ h)

theorem generator_mem_of_infinite {m t : ℕ} (family : Fin m → Set ℕ)
    (xs : Fin (t + 1) → ℕ) (ys : Fin t → ℕ)
    (hC : (roundCore family xs).Infinite) :
    generator family t xs ys ∈ roundCore family xs := by
  classical
  simp [generator, hC, leastFresh_mem]

theorem generator_le_of_available {m t : ℕ} (family : Fin m → Set ℕ)
    (xs : Fin (t + 1) → ℕ) (ys : Fin t → ℕ)
    (hC : (roundCore family xs).Infinite) {z : ℕ}
    (hzC : z ∈ roundCore family xs)
    (hzx : z ∉ historySet xs) (hzy : z ∉ historySet ys) :
    generator family t xs ys ≤ z := by
  classical
  simp only [generator, hC, dif_pos]
  apply leastFresh_le _ hC _ hzC
  simp only [Finset.mem_union, not_or]
  exact ⟨hzx, hzy⟩



def run (gen : OnlineGenerator) (input : Stream) : Stream
  | 0 => gen 0 (fun i => input i) (fun i => Fin.elim0 i)
  | t + 1 => gen (t + 1) (fun i => input i) (fun i => run gen input i)

theorem run_eq (gen : OnlineGenerator) (input : Stream) (t : ℕ) :
    run gen input t = gen t (fun i => input i) (fun i => run gen input i) := by
  cases t with
  | zero =>
      unfold run
      congr
      funext i
      exact Fin.elim0 i
  | succ t =>
      unfold run
      rfl

theorem follows_run (gen : OnlineGenerator) (input : Stream) :
    Follows gen input (run gen input) := by
  intro t
  exact run_eq gen input t

theorem historySet_input (input : Stream) (t : ℕ) :
    historySet (fun i : Fin t => input i) = Generic.sample input t := by
  exact Generic.sequenceSample_prefix input t

theorem run_fresh_input {m : ℕ} (family : Fin m → Set ℕ)
    (input : Stream) (t : ℕ) :
    run (generator family) input t ∉ Generic.sample input (t + 1) := by
  rw [run_eq, ← historySet_input]
  exact generator_not_input family _ _

theorem run_fresh_output {m : ℕ} (family : Fin m → Set ℕ)
    (input : Stream) {s t : ℕ} (hst : s < t) :
    run (generator family) input s ≠ run (generator family) input t := by
  intro heq
  have hmem : run (generator family) input s ∈
      historySet (fun i : Fin t => run (generator family) input i) := by
    unfold historySet
    rw [Generic.mem_sequenceSample_iff]
    exact ⟨⟨s, hst⟩, rfl⟩
  have hnot : run (generator family) input t ∉
      historySet (fun i : Fin t => run (generator family) input i) := by
    rw [run_eq]
    exact generator_not_output family _ _
  exact hnot (heq ▸ hmem)

theorem run_injective {m : ℕ} (family : Fin m → Set ℕ)
    (input : Stream) : Function.Injective (run (generator family) input) := by
  intro s t hst
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact run_fresh_output family input hlt hst
  · exact run_fresh_output family input hgt hst.symm


theorem not_streamIn_exists {input : Stream} {L : Set ℕ}
    (h : ¬ StreamIn input L) : ∃ s, input s ∉ L := by
  obtain ⟨x, ⟨s, rfl⟩, hx⟩ := Set.not_subset.mp h
  exact ⟨s, hx⟩

theorem eventually_roundCore_eq_informationCore {m : ℕ}
    (family : Fin m → Set ℕ) (input : Stream) :
    ∃ T, ∀ t, T ≤ t →
      roundCore family (fun i : Fin (t + 1) => input i) =
        informationCore family input := by
  classical
  let badTime : Fin m → ℕ := fun j =>
    if h : ¬ StreamIn input (family j) then
      Classical.choose (not_streamIn_exists h)
    else 0
  let T := ∑ j : Fin m, (badTime j + 1)
  refine ⟨T, ?_⟩
  intro t ht
  ext z
  simp only [roundCore, informationCore, Set.mem_setOf_eq]
  constructor
  · intro hz j hj
    apply hz j
    intro i
    exact hj ⟨i, rfl⟩
  · intro hz j hjprefix
    apply hz j
    intro x hxrange
    rcases hxrange with ⟨s, rfl⟩
    by_contra hnot
    have hbad : ¬ StreamIn input (family j) := by
      intro hall
      exact hnot (hall ⟨s, rfl⟩)
    have hchosen : input (badTime j) ∉ family j := by
      simp only [badTime, dif_pos hbad]
      exact Classical.choose_spec (not_streamIn_exists hbad)
    have hle : badTime j + 1 ≤ T := by
      apply Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    have hslt : badTime j < t + 1 := lt_of_lt_of_le (Nat.lt_succ_self _) (hle.trans ht)
    exact hchosen (hjprefix ⟨badTime j, hslt⟩)

end Stage3Case017Proof
theorem stage3_result : Stage3Case017.MainClaim := by sorry
