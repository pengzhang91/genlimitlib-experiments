import Case025Helpers

open Stage3Case025

/-- Checked semantic core of the positive-presentation engine: the same online
rule works for the whole indexed family and, on every exact positive
presentation, has a following trajectory which is eventually target-valid,
current-round input-fresh, and globally nonrepeating. -/
theorem stage3_positive_eventual_novel :
    ∀ family : ℕ → Language, (∀ i, (family i).Infinite) →
      ∃ gen : OnlineGenerator,
        ∀ i (input : Stream), GenLimit.Presents input (family i) →
          ∃ output : Stream,
            Follows gen input output ∧
            GenLimit.NovelGeneratesInLimit input output (family i) := by
  intro family hfamily
  refine ⟨Case025.patientGenerator family hfamily, ?_⟩
  intro i input hpresents
  refine ⟨Case025.trajectory (Case025.patientGenerator family hfamily) input, ?_⟩
  exact ⟨Case025.trajectory_follows _ _,
    Case025.patient_novel_generates family hfamily i input hpresents⟩
