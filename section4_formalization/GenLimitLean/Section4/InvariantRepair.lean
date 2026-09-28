import GenLimit.Paper13_ParetoOptimalNonuniformGeneration.ArbitraryScheduler

/-! The Section 4.1 proof repair, including the published scheduler on histories
with repetitions. The existing P13 generator schedules by distinct sample size;
the definition below schedules by the actual round count as the paper does. -/

namespace Section4.InvariantRepair

open GenLimit.ParetoGeneration

variable {α : Type*} [Infinite α]

noncomputable def roundSchedulerGenerator (F : ℕ → Set α) (f : ℕ → ℕ) :
    HistoryGenerator α := by
  classical
  exact fun t xs =>
    let sample := GenLimit.Generic.sequenceSample xs
    let selected := greedyListScan F sample ∅ (schedulerScanOrder F f t)
    GenLimit.Support.freshFromInfinite (indexedIntersection F selected)
      (greedyListScan_core_infinite F sample ∅ (schedulerScanOrder F f t)
        (by simpa using (Set.infinite_univ : (Set.univ : Set α).Infinite))) sample

theorem roundSchedulerGenerator_spec (F : ℕ → Set α) (f : ℕ → ℕ)
    {t : ℕ} (xs : Fin t → α) :
    roundSchedulerGenerator F f t xs ∈
        indexedIntersection F (greedyListScan F
          (GenLimit.Generic.sequenceSample xs) ∅ (schedulerScanOrder F f t)) ∧
      roundSchedulerGenerator F f t xs ∉ GenLimit.Generic.sequenceSample xs := by
  classical
  simp only [roundSchedulerGenerator]
  exact ⟨GenLimit.Support.freshFromInfinite_mem _ _ _,
    GenLimit.Support.freshFromInfinite_not_mem _ _ _⟩

/-- Published Theorem 8 with repetitions allowed: the threshold concerns the
number of distinct observed points, while f is evaluated at the actual round. -/
theorem published_theorem_8_with_repetitions
    (F : ℕ → Set α) (f : ℕ → ℕ) (hf : IsUnboundedScheduler f)
    {i t : ℕ} (xs : Fin t → α)
    (hthreshold : schedulerTimeVector F f hf i ≤
      (GenLimit.Generic.sequenceSample xs).card)
    (hTarget : ∀ k, xs k ∈ F i) :
    roundSchedulerGenerator F f t xs ∈ F i ∧
      ∀ k, roundSchedulerGenerator F f t xs ≠ xs k := by
  classical
  let sample := GenLimit.Generic.sequenceSample xs
  have hsample_le : sample.card ≤ t := by
    dsimp [sample, GenLimit.Generic.sequenceSample]
    exact (Finset.card_image_le).trans (by simp)
  have hentry : schedulerEntryTime f hf i ≤ t :=
    ((Nat.le_max_left _ _).trans hthreshold).trans hsample_le
  have hiScope : i < f t := (schedulerEntryTime_le_iff f hf).mp hentry
  let current := canonicalProcedureStage F (f t)
  have hiOrder : i ∈ current.order := by
    apply current.order_perm.mem_iff.mpr
    exact List.mem_range.mpr hiScope
  obtain ⟨before, after, hOrder⟩ := List.mem_iff_append.mp hiOrder
  have hScanOrder : schedulerScanOrder F f t = before ++ i :: after := by
    simpa [schedulerScanOrder, current] using hOrder
  have hSampleTarget : (↑sample : Set α) ⊆ F i :=
    GenLimit.Generic.sequenceSample_subset_of_pointwise hTarget
  have hcomplexity : current.complexity i = canonicalComplexity F i :=
    canonicalProcedureStage_complexity_stable F hiScope
  have hcard : canonicalComplexity F i < sample.card := by
    have hb := (Nat.le_max_right _ _).trans hthreshold
    exact Nat.lt_of_succ_le hb
  have hiSelected : i ∈ greedyListScan F sample ∅ (schedulerScanOrder F f t) :=
    target_selected_in_greedyListScan F sample hScanOrder
      (by simpa [hcomplexity] using current.max_bounds before i after hOrder)
      hSampleTarget hcard
  have hspec := roundSchedulerGenerator_spec F f xs
  constructor
  · exact hspec.1 i hiSelected
  · intro k hk
    exact hspec.2 (GenLimit.Generic.mem_sequenceSample_iff.mpr ⟨k, hk.symm⟩)

end Section4.InvariantRepair

#print axioms GenLimit.ParetoGeneration.literal_claim_3_2_counterexample
#print axioms GenLimit.ParetoGeneration.maxScoreBound_persists_insert
#print axioms GenLimit.ParetoGeneration.InsertionSplit.orderMaxScoreBounds
#print axioms GenLimit.ParetoGeneration.target_selected_in_greedyListScan
#print axioms GenLimit.ParetoGeneration.theorem_4_arbitrary_scheduler
#print axioms GenLimit.ParetoGeneration.overview_theorem_1_semantic
#print axioms Section4.InvariantRepair.published_theorem_8_with_repetitions
