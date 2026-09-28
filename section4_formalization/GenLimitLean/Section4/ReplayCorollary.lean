import Section4.ReplayChanges
import Section4.ReplayMinimal

/-! A single checked endpoint collects the written finite-state corollary,
including an explicit state machine that realizes the same P22 generator. -/
namespace Section4.Replay

open Set
open GenLimit.Replay

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

noncomputable def canonicalGenerator (L : ι → Set α) : ProperGenerator ι α :=
  generator L (minimalFirstChoice L) (minimalLowerChoice L)

/-- Complete finite-state/output-change/minimal-language corollary.
The state count is the exact cardinality of the exhibited Mealy state type;
not every state need be reachable. The change bound holds on every finite
prefix and therefore bounds the total number of changes on an infinite run. -/
theorem finite_state_replay_corollary (L : ι → Set α) (hc : Criterion L) :
    IsProperLimitReplayGenerator L (canonicalGenerator L) ∧
    (∀ s n, MinimalLanguage L (properOutput (canonicalGenerator L) s (n + 1))) ∧
    (∀ target s, IsProperReplayEnumeration L (canonicalGenerator L) target s →
      (∃ h, L h ⊆ L target ∧ ∃ B, ∀ n, B ≤ n →
        properOutput (canonicalGenerator L) s n = h) ∧
      (∀ n, L (properOutput (canonicalGenerator L) s (n + 1)) \ L target ⊆
        L (properOutput (canonicalGenerator L) s 1)) ∧
      (∀ n, changeCount (fun t => properOutput (canonicalGenerator L) s (t + 1)) n ≤
        Fintype.card ι)) ∧
    Fintype.card (MachineState ι) = 1 + Fintype.card ι * 2 ^ Fintype.card ι ∧
    (∀ s n,
      emit L (minimalFirstChoice L) (minimalLowerChoice L)
        (machineRun (minimalFirstChoice L) (fun t => profile L (s t)) n)
        (profile L (s n)) = properOutput (canonicalGenerator L) s (n + 1)) := by
  refine ⟨minimal_generator_correct L hc, minimal_generator_outputs L, ?_, machine_state_card, ?_⟩
  · intro target s htext
    have hx := first_observation_mem L (canonicalGenerator L) target s htext.1
    have hgood := minimalFirstChoice_spec L hc (s 0) ⟨target, hx⟩
    have hlower := minimalLowerChoice_spec L
    refine ⟨generator_stabilizes L _ _ hlower target s hgood htext, ?_, ?_⟩
    · intro n x hxout
      have hi := (generator_invariants L _ _ hlower target s hgood htext.1 (n + 1) (by omega)).2 hxout.1
      rw [canonicalGenerator, generator_output_one]
      exact hi.resolve_right hxout.2
    · intro n
      exact generator_change_bound L _ _ hlower target s hgood htext.1 n
  · intro s n
    exact profile_machine_realizes L _ _ s n

end Section4.Replay
