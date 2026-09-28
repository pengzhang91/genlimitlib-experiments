import GenLimit.Core.OnlineGeneration
import GenLimit.Paper17_InfiniteContamination.Definitions
import GenLimit.Paper39_DenseGeneration.Abstract.Announcements
import GenLimit.Paper39_DenseGeneration.Abstract.PatientScope
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Topology.Order.LiminfLimsup

/-!
Shared Case 024 specification for every evidence condition.

The statement reuses the research library's predicates for eventual novel
generation, generator-first announcements, and repetition-free full
enumerations with vanishing noise.  The only local mathematical definition is
the target-relative upper density induced by ambient natural-number prefixes;
the library currently exposes the corresponding lower density but not this
upper-density variant.

The existential targets and stream occur before every generator, probability
space, and random seed.  A generator receives only the common input history
and its own output history: neither a target identifier nor target-membership
feedback occurs in its type.  The same random trajectory is used for every
target interpretation.
-/

open Filter MeasureTheory
open scoped Topology

namespace Stage3Case024

/-- The library's countable-universe language type. -/
abbrev Language := GenLimit.Language

/-- The library's stream type specialized to natural numbers. -/
abbrev Stream := GenLimit.Generic.Stream ℕ

/-- At round `t`, the generator sees the input through the current round and
its own outputs strictly before the current round.  The library's generic
generator sees only the strictly earlier input prefix, so it is not
substituted for this case-specific timing interface. -/
abbrev OnlineGenerator :=
  (t : ℕ) → (Fin (t + 1) → ℕ) → (Fin t → ℕ) → ℕ

/-- A randomized generator is an online rule selected by its internal seed. -/
abbrev RandomizedGenerator (Ω : Type) := Ω → OnlineGenerator

/-- The output stream is the trajectory produced by the online rule. -/
def Follows (gen : OnlineGenerator) (input output : Stream) : Prop :=
  ∀ t, output t = gen t (fun i => input i) (fun i => output i)

/-- One coupled random output trajectory follows the same seeded generator. -/
def RandomFollows {Ω : Type} (gen : RandomizedGenerator Ω)
    (input : Stream) (output : Ω → Stream) : Prop :=
  ∀ ω, Follows (gen ω) input (output ω)

/-- Target-relative upper density in the common ambient natural-number order.
The intersection makes the numerator count only scored target elements. -/
noncomputable def relativeUpperDensity (A K : Language) : ℝ :=
  limsup
    (fun n : ℕ =>
      (GenLimit.PatientScope.prefixCount (A ∩ K) n : ℝ) /
        (GenLimit.PatientScope.prefixCount K n : ℝ))
    atTop

/-- A fixed stream is a legal presentation of an infinite target.  The
library predicate packages injectivity, full coverage, and vanishing empirical
noise. -/
def Legal (input : Stream) (K : Language) : Prop :=
  K.Infinite ∧
    GenLimit.InfiniteContamination.VanishingNoiseEnumeration input K

/-- The random trajectory is measurable coordinate by coordinate. -/
def CoordinatewiseMeasurable {Ω : Type} [MeasurableSpace Ω]
    (output : Ω → Stream) : Prop :=
  ∀ t, Measurable (fun ω => output ω t)

/-- Eventual success has one seed-dependent finite threshold on an almost-sure
event.  `NovelGeneratesInLimit` requires target validity, avoidance of the
input through the current round, and no repeated generator output. -/
def EventuallyFreshValid {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) (K : Language) (input : Stream)
    (output : Ω → Stream) : Prop :=
  ∀ᵐ ω ∂μ, GenLimit.NovelGeneratesInLimit input (output ω) K

/-- Integrability is the explicit well-definedness condition for the displayed
real-valued expectation. -/
def DensityIntegrable {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) (K : Language) (input : Stream)
    (output : Ω → Stream) : Prop :=
  Integrable
    (fun ω => relativeUpperDensity
      (GenLimit.GeneratorFirst input (output ω)) K) μ

/-- Expectation is outside the pathwise upper limit. -/
noncomputable def expectedUpperDensity {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) (K : Language) (input : Stream)
    (output : Ω → Stream) : ℝ :=
  ∫ ω, relativeUpperDensity
    (GenLimit.GeneratorFirst input (output ω)) K ∂μ

/-- The required two-target obstruction on one fixed common stream. -/
def PairObstruction (K₀ K₁ : Language) (input : Stream) : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω)
      [IsProbabilityMeasure μ]
      (gen : RandomizedGenerator Ω) (output : Ω → Stream),
    RandomFollows gen input output →
    CoordinatewiseMeasurable output →
    DensityIntegrable μ K₀ input output →
    DensityIntegrable μ K₁ input output →
    EventuallyFreshValid μ K₀ input output →
    EventuallyFreshValid μ K₁ input output →
      expectedUpperDensity μ K₀ input output +
          expectedUpperDensity μ K₁ input output ≤ 1 ∧
        ¬ ((1 / 2 : ℝ) < expectedUpperDensity μ K₀ input output ∧
           (1 / 2 : ℝ) < expectedUpperDensity μ K₁ input output)

/-- Deterministic pathwise eventual validity and freshness. -/
def EventuallyFreshValidPath
    (K : Language) (input output : Stream) : Prop :=
  GenLimit.NovelGeneratesInLimit input output K

/-- Exact strict nesting of an indexed finite family. -/
def StrictlyNested {r : ℕ} (family : Fin r → Language) : Prop :=
  ∀ (i j : Fin r), (i : ℕ) < (j : ℕ) → family i ⊂ family j

/-- A target-independent deterministic generator works on every stream legal
for all members of the known family.  A displayed common legal stream then
makes the simultaneous-validity class nonempty. -/
def GloballyFeasible {r : ℕ} (family : Fin r → Language) : Prop :=
  ∃ gen : OnlineGenerator, ∀ input : Stream,
    (∀ j, Legal input (family j)) →
      ∃ output : Stream,
        Follows gen input output ∧
          ∀ j, EventuallyFreshValidPath (family j) input output

/-- Every admissible randomized generator simultaneously valid on the common
stream has a member of the family with expected upper density exactly zero. -/
def ManyTargetObstruction {r : ℕ}
    (family : Fin r → Language) (input : Stream) : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω)
      [IsProbabilityMeasure μ]
      (gen : RandomizedGenerator Ω) (output : Ω → Stream),
    RandomFollows gen input output →
    CoordinatewiseMeasurable output →
    (∀ j, DensityIntegrable μ (family j) input output) →
    (∀ j, EventuallyFreshValid μ (family j) input output) →
      ∃ j, expectedUpperDensity μ (family j) input output = 0

/-- The optional finite-family strengthening: exactly `r` strictly nested
infinite targets share one legal stream, the globally valid class is nonempty,
and its fixed-stream worst member has value zero. -/
def ManyTargetWitness {r : ℕ}
    (family : Fin r → Language) (input : Stream) : Prop :=
  StrictlyNested family ∧
    (∀ j, Legal input (family j)) ∧
    GloballyFeasible family ∧
    ManyTargetObstruction family input

/-- Exact Stage 3 target: the mandatory nested pair and the optional stronger
finite-many-target zero-minimax construction. -/
def MainClaim : Prop :=
  (∃ K₀ K₁ : Language, ∃ input : Stream,
    K₀ ⊂ K₁ ∧ Legal input K₀ ∧ Legal input K₁ ∧
      PairObstruction K₀ K₁ input) ∧
  (∀ r : ℕ, 2 ≤ r →
    ∃ family : Fin r → Language, ∃ input : Stream,
      ManyTargetWitness family input)

end Stage3Case024
