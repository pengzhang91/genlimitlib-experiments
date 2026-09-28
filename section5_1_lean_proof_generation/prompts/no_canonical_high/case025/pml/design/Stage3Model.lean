import GenLimit.Core.FiniteContamination
import GenLimit.Core.OnlineGeneration
import GenLimit.Paper39_DenseGeneration.Abstract.Announcements
import GenLimit.Paper39_DenseGeneration.Abstract.TargetDensity

/-!
Shared Case 025 specification for every evidence condition.

The statement reuses the research library's exact vocabulary for languages,
streams, positive presentations, finite occurrence-counted contamination,
eventual novel generation, first announcements, ambient-prefix relative lower
density, and prefix counts.  Only the within-round online timing and its trace
relation remain case-local: the generator observes the current presenter move
and its own strictly earlier outputs.

The generator is chosen for the whole indexed family before the target index
and presentation.  It receives neither a target identifier nor membership
feedback.  Input repetitions are permitted and count as actual rounds.
-/

namespace Stage3Case025

/-- The research library's countable-universe language type. -/
abbrev Language := GenLimit.Language

/-- The research library's stream type specialized to natural numbers. -/
abbrev Stream := GenLimit.Generic.Stream ℕ

/-- At round `t`, the generator sees the input through the current round and
its own outputs strictly before the current round. -/
abbrev OnlineGenerator :=
  (t : ℕ) → (Fin (t + 1) → ℕ) → (Fin t → ℕ) → ℕ

/-- The output stream is the trajectory produced by the online rule. -/
def Follows (gen : OnlineGenerator) (input output : Stream) : Prop :=
  ∀ t, output t = gen t (fun i => input i) (fun i => output i)

/-- Complete coverage with finitely many off-target occurrence rounds.
Unlike the P17 injective finite-noise predicates, this permits arbitrary
repetitions and counts bad time indices rather than distinct bad values. -/
def CompleteFiniteOccurrencePresentation
    (input : Stream) (K : Language) : Prop :=
  K ⊆ Set.range input ∧
    GenLimit.Generic.FinitelyManyViolations input (fun x => x ∈ K)

/-- Presentation-dependent half density for every indexed countable family.
`GeneratorFirst` implements the presenter-first same-round tie convention;
the explicit intersection scores only target values. -/
def PresentationDependentHalfDensity : Prop :=
  ∀ family : ℕ → Language, (∀ i, (family i).Infinite) →
    ∃ gen : OnlineGenerator,
      ∀ i (input : Stream),
        CompleteFiniteOccurrencePresentation input (family i) →
          ∃ output : Stream,
            Follows gen input output ∧
            GenLimit.NovelGeneratesInLimit input output (family i) ∧
            (1 / 2 : ℝ) ≤
              GenLimit.PatientScope.relativeLowerDensity
                (GenLimit.GeneratorFirst input output ∩ family i)
                (family i)

/-- The positive-presentation half-density engine isolated from Section 4.
`GenLimit.Presents` allows repeated rounds and requires exact range equality. -/
def PositivePresentationHalfDensity : Prop :=
  ∀ family : ℕ → Language, (∀ i, (family i).Infinite) →
    ∃ gen : OnlineGenerator,
      ∀ i (input : Stream), GenLimit.Presents input (family i) →
        ∃ output : Stream,
          Follows gen input output ∧
          GenLimit.NovelGeneratesInLimit input output (family i) ∧
          (1 / 2 : ℝ) ≤
            GenLimit.PatientScope.relativeLowerDensity
              (GenLimit.GeneratorFirst input output ∩ family i)
              (family i)

/-- The finite-addition/no-omission transfer isolated from Section 5. -/
def FiniteNoiseTransferPrinciple : Prop :=
  PositivePresentationHalfDensity → PresentationDependentHalfDensity

/-- Exact Stage 3 target: the presentation-dependent half-density theorem. -/
def MainClaim : Prop := PresentationDependentHalfDensity

end Stage3Case025

