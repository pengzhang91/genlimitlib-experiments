import output.Helpers

open Stage3Case025

/-- Checked partial milestone: for every indexed family of infinite languages,
the patient-stack rule has a trajectory that follows the rule, avoids the
presenter through the current round, and never repeats an earlier output. -/
theorem stage3_checked_global_fresh :
    ∀ family : ℕ → Language, (∀ i, (family i).Infinite) →
      ∃ gen : OnlineGenerator,
        ∀ input : Stream,
          ∃ output : Stream,
            Follows gen input output ∧
            ∀ t, output t ∉ GenLimit.sample input (t + 1) ∧
              ∀ s, s < t → output s ≠ output t := by
  exact Case025.uniform_global_fresh_generator

/-- Once eventual containment of the machine focus is established, the same
checked trajectory immediately satisfies the library's full novelty predicate. -/
theorem stage3_checked_novel_from_focus
    (family : ℕ → Language) (hfamily : ∀ i, (family i).Infinite)
    (input : Stream) (target : Language)
    (hfocus : ∃ T, ∀ t, T ≤ t →
      Case025.topFocus
        (Case025.run family (List.ofFn (fun i : Fin (t + 1) => input i))) ⊆ target) :
    GenLimit.NovelGeneratesInLimit input
      (Case025.trajectory (Case025.generator family) input) target := by
  exact Case025.trajectory_novel_of_eventual_focus family hfamily input target hfocus
