import GenLimit.Core.OnlineGeneration
import GenLimit.Core.PartialPresentation
import GenLimit.Paper39_DenseGeneration.Abstract.Announcements
import GenLimit.Paper39_DenseGeneration.Abstract.TargetDensity

/-!
Shared Case 017 specification for every evidence condition.

The target deliberately uses the existing research-library vocabulary for
partial presentations, eventual novel generation, first announcements, and
target-relative lower density.  Only the genuinely case-specific interfaces
remain local: the within-round online timing, the information core of a finite
family, and the family-level success predicate.

This file contains definitions and the exact proposition only.  It contains no
generator construction or proof of the density bound.
-/

namespace Stage3Case017

/-- The library's countable-universe language type. -/
abbrev Language := GenLimit.Language

/-- The library's stream type specialized to natural numbers. -/
abbrev Stream := GenLimit.Generic.Stream ℕ

/-- At round `t`, the generator sees the input through the current round and
its own outputs strictly before the current round.  The standard library
`Generator` sees only a strictly earlier input prefix, so it is not substituted
for this case-specific timing interface. -/
abbrev OnlineGenerator :=
  (t : ℕ) → (Fin (t + 1) → ℕ) → (Fin t → ℕ) → ℕ

/-- The output stream is the trajectory produced by the online rule. -/
def Follows (gen : OnlineGenerator) (input output : Stream) : Prop :=
  ∀ t, output t = gen t (fun i => input i) (fun i => output i)

/-- The information core is the intersection of all family members containing
the presented stream.  Compatibility uses the library predicate `StreamIn`. -/
def informationCore {m : ℕ} (family : Fin m → Language)
    (input : Stream) : Language :=
  {z | ∀ j, GenLimit.Generic.StreamIn input (family j) → z ∈ family j}

/-- One family-tailored generator succeeds simultaneously for every compatible
target and every injective infinite partial presentation.

`InfinitePartialPresentation`, `NovelGeneratesInLimit`, `GeneratorFirst`, and
`relativeLowerDensity` are existing research-library vocabulary. -/
def SucceedsFor {m : ℕ} (family : Fin m → Language)
    (gen : OnlineGenerator) : Prop :=
  ∀ input : Stream,
    Function.Injective input →
    (∃ j, GenLimit.Generic.InfinitePartialPresentation input (family j)) →
    (informationCore family input).Infinite →
    ∃ output : Stream,
      Follows gen input output ∧
      ∀ j, GenLimit.Generic.StreamIn input (family j) →
        GenLimit.NovelGeneratesInLimit input output (family j) ∧
        max
            ((1 / 2 : ℝ) *
              GenLimit.PatientScope.relativeLowerDensity
                (informationCore family input) (family j))
            (GenLimit.PatientScope.relativeLowerDensity
              (informationCore family input \ Set.range input) (family j))
          ≤ GenLimit.PatientScope.relativeLowerDensity
              (GenLimit.GeneratorFirst input output ∩ family j) (family j)

/-- Exact Stage 3 target.  The generator is chosen for the family before the
presentation and compatible target.  No uniform family-to-program compiler,
runtime bound, query bound, or sample-complexity bound is asserted. -/
def MainClaim : Prop :=
  ∀ (m : ℕ),
    0 < m →
    ∀ family : Fin m → Language,
      (∀ j, (family j).Infinite) →
      ∃ gen : OnlineGenerator, SucceedsFor family gen

end Stage3Case017
