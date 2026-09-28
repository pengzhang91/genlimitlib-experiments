import Stage3Model

open Filter
open scoped Topology

namespace Stage3Case025

/-- A language is consistent with the presenter history through round `t`. -/
def HistoryConsistent
    (family : ℕ → Language) (input : Stream) (t i : ℕ) : Prop :=
  ∀ s, s ≤ t → input s ∈ family i

/-- The descending critical chain from the Kleinberg--Mullainathan construction. -/
def Critical
    (family : ℕ → Language) (input : Stream) (t : ℕ) : (i : ℕ) → Prop
  | i =>
      HistoryConsistent family input t i ∧
        ∀ j, j < i → Critical family input t j → family i ⊆ family j
termination_by i => i

private theorem target_history_consistent
    {family : ℕ → Language} {input : Stream} {i t : ℕ}
    (hp : GenLimit.Presents input (family i)) :
    HistoryConsistent family input t i := by
  intro s hs
  rw [GenLimit.Presents] at hp
  exact hp ▸ Set.mem_range_self s

private theorem eventually_inconsistent_of_not_subset
    {family : ℕ → Language} {input : Stream} {i j : ℕ}
    (hp : GenLimit.Presents input (family i))
    (hsub : ¬ family i ⊆ family j) :
    ∀ᶠ t in atTop, ¬ HistoryConsistent family input t j := by
  obtain ⟨x, hxi, hxj⟩ := Set.not_subset.mp hsub
  rw [GenLimit.Presents] at hp
  obtain ⟨s, rfl⟩ := hp.symm.subset hxi
  filter_upwards [eventually_ge_atTop s] with t hst
  intro hc
  exact hxj (hc s hst)

private theorem eventually_consistent_implies_target_subset
    {family : ℕ → Language} {input : Stream} {i j : ℕ}
    (hp : GenLimit.Presents input (family i)) :
    ∀ᶠ t in atTop,
      HistoryConsistent family input t j → family i ⊆ family j := by
  by_cases hsub : family i ⊆ family j
  · exact Filter.Eventually.of_forall fun _ _ => hsub
  · filter_upwards [eventually_inconsistent_of_not_subset hp hsub] with t ht hc
    exact (ht hc).elim

/-- Under an exact positive presentation, the target language eventually belongs
to the critical chain. -/
theorem target_eventually_critical
    {family : ℕ → Language} {input : Stream} {i : ℕ}
    (hp : GenLimit.Presents input (family i)) :
    ∀ᶠ t in atTop, Critical family input t i := by
  have hall : ∀ j ∈ Finset.range i,
      ∀ᶠ t in atTop,
        HistoryConsistent family input t j → family i ⊆ family j := by
    intro j hj
    exact eventually_consistent_implies_target_subset hp
  have hevent : ∀ᶠ t in atTop, ∀ j ∈ Finset.range i,
      HistoryConsistent family input t j → family i ⊆ family j := by
    exact (Finset.eventually_all (Finset.range i)).2 hall
  filter_upwards [hevent] with t ht
  rw [Critical]
  refine ⟨target_history_consistent hp, ?_⟩
  intro j hji hjcrit
  rw [Critical] at hjcrit
  exact ht j (Finset.mem_range.2 hji) hjcrit.1

end Stage3Case025

namespace Stage3Case025

/-- Criticality computed directly from the finite presenter history available to
an online generator. -/
def SeqCritical
    (family : ℕ → Language) {t : ℕ} (xs : Fin (t + 1) → ℕ) : (i : ℕ) → Prop
  | i =>
      (∀ s, xs s ∈ family i) ∧
        ∀ j, j < i → SeqCritical family xs j → family i ⊆ family j
termination_by i => i

private theorem seqCritical_iff
    (family : ℕ → Language) (input : Stream) (t i : ℕ) :
    SeqCritical family (fun k : Fin (t + 1) => input k) i ↔
      Critical family input t i := by
  induction i using Nat.strong_induction_on with
  | h i ih =>
      rw [SeqCritical, Critical]
      constructor
      · rintro ⟨hc, hchain⟩
        refine ⟨?_, ?_⟩
        · intro s hs
          exact hc ⟨s, Nat.lt_succ_iff.2 hs⟩
        · intro j hji hj
          exact hchain j hji ((ih j hji).2 hj)
      · rintro ⟨hc, hchain⟩
        refine ⟨?_, ?_⟩
        · intro s
          exact hc s (Nat.le_of_lt_succ s.isLt)
        · intro j hji hj
          exact hchain j hji ((ih j hji).1 hj)

noncomputable def positiveFocus
    (family : ℕ → Language) {t : ℕ} (xs : Fin (t + 1) → ℕ) : ℕ := by
  classical
  exact Nat.findGreatest (SeqCritical family xs) t

noncomputable def historyUsed {t : ℕ}
    (xs : Fin (t + 1) → ℕ) (ys : Fin t → ℕ) : Finset ℕ :=
  Finset.univ.image xs ∪ Finset.univ.image ys

noncomputable def positiveGenerator
    (family : ℕ → Language) (hinfinite : ∀ i, (family i).Infinite) :
    OnlineGenerator :=
  fun t xs ys =>
    Classical.choose
      ((hinfinite (positiveFocus family xs)).exists_not_mem_finset
        (historyUsed xs ys))

private theorem positiveGenerator_mem
    {family : ℕ → Language} {hinfinite : ∀ i, (family i).Infinite}
    {t : ℕ} {xs : Fin (t + 1) → ℕ} {ys : Fin t → ℕ} :
    positiveGenerator family hinfinite t xs ys ∈
      family (positiveFocus family xs) := by
  exact (Classical.choose_spec
    ((hinfinite (positiveFocus family xs)).exists_not_mem_finset
      (historyUsed xs ys))).1

private theorem positiveGenerator_fresh
    {family : ℕ → Language} {hinfinite : ∀ i, (family i).Infinite}
    {t : ℕ} {xs : Fin (t + 1) → ℕ} {ys : Fin t → ℕ} :
    positiveGenerator family hinfinite t xs ys ∉ historyUsed xs ys := by
  exact (Classical.choose_spec
    ((hinfinite (positiveFocus family xs)).exists_not_mem_finset
      (historyUsed xs ys))).2

noncomputable def trajectory (gen : OnlineGenerator) (input : Stream) : Stream :=
  fun t => gen t (fun i => input i) (fun i => trajectory gen input i)
termination_by t => t

private theorem trajectory_follows (gen : OnlineGenerator) (input : Stream) :
    Follows gen input (trajectory gen input) := by
  intro t
  rw [trajectory]

/-- The KM critical-chain generator gives the full eventual novelty conclusion
for every exact positive presentation. -/
theorem positive_eventual_novel_generation :
    ∀ family : ℕ → Language, (∀ i, (family i).Infinite) →
      ∃ gen : OnlineGenerator,
        ∀ i (input : Stream), GenLimit.Presents input (family i) →
          ∃ output : Stream,
            Follows gen input output ∧
              GenLimit.NovelGeneratesInLimit input output (family i) := by
  intro family hinfinite
  classical
  refine ⟨positiveGenerator family hinfinite, ?_⟩
  intro i input hp
  let output := trajectory (positiveGenerator family hinfinite) input
  refine ⟨output, trajectory_follows _ _, ?_⟩
  rw [GenLimit.NovelGeneratesInLimit]
  have hevent := target_eventually_critical hp
  rw [eventually_atTop] at hevent
  obtain ⟨T, hT⟩ := hevent
  refine ⟨max T i, ?_⟩
  intro t hmax
  have ht : Critical family input t i := hT t (le_trans (le_max_left T i) hmax)
  have hit : i ≤ t := le_trans (le_max_right T i) hmax
  have hseq : SeqCritical family (fun k : Fin (t + 1) => input k) i :=
    (seqCritical_iff family input t i).2 ht
  have hfocus : SeqCritical family (fun k : Fin (t + 1) => input k)
      (positiveFocus family (fun k : Fin (t + 1) => input k)) :=
    Nat.findGreatest_spec hit hseq
  have hifocus : i ≤ positiveFocus family (fun k : Fin (t + 1) => input k) :=
    Nat.le_findGreatest hit hseq
  rw [SeqCritical] at hfocus
  have hsubset : family (positiveFocus family (fun k : Fin (t + 1) => input k)) ⊆
      family i := by
    by_cases hEq : i = positiveFocus family (fun k : Fin (t + 1) => input k)
    · simpa [hEq]
    · exact hfocus.2 i (lt_of_le_of_ne hifocus hEq) hseq
  have hmem := positiveGenerator_mem
    (family := family) (hinfinite := hinfinite)
    (xs := fun k : Fin (t + 1) => input k)
    (ys := fun k : Fin t => output k)
  have hfresh := positiveGenerator_fresh
    (family := family) (hinfinite := hinfinite)
    (xs := fun k : Fin (t + 1) => input k)
    (ys := fun k : Fin t => output k)
  have hout : output t = positiveGenerator family hinfinite t
      (fun k => input k) (fun k => output k) := by
    exact trajectory_follows _ _ t
  rw [hout]
  refine ⟨hsubset hmem, ?_, ?_⟩
  · intro hsamp
    rw [GenLimit.sample] at hsamp
    obtain ⟨s, hs, hst⟩ := Finset.mem_image.mp hsamp
    apply hfresh
    apply Finset.mem_union_left
    exact Finset.mem_image.mpr ⟨⟨s, Finset.mem_range.mp hs⟩, Finset.mem_univ _, hst⟩
  · intro s hst heq
    apply hfresh
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨⟨s, hst⟩, Finset.mem_univ _, heq⟩

end Stage3Case025
