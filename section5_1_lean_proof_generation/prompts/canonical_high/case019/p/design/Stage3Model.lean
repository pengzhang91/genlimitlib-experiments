import GenLimit.Core.FiniteContamination
import GenLimit.Core.OnlineGeneration
import GenLimit.Paper39_DenseGeneration.Abstract.Announcements
import GenLimit.Paper39_DenseGeneration.Abstract.TargetDensity
import Mathlib.Data.Int.Basic
import Mathlib.Data.Set.Countable

/-!
Shared Case 019 specification for every evidence condition.

The statement reuses the research library's generic languages, indexed
families, extensional language classes, streams, semantic prefix generators,
injective value-contaminated presentations, natural-number novelty predicate,
first-announcement set, and ambient-prefix relative lower density.

At paper round `t`, the current input arrives before the output.  Therefore
`outputAfterInput gen input t` runs the library prefix generator on the first
`t + 1` inputs.  The local polymorphic novelty and first-announcement
predicates are needed only for the integer-valued separation clause: the
corresponding library declarations are currently specialized to `Nat`.
-/

namespace Stage3Case019

abbrev Language (α : Type*) := GenLimit.Generic.Language α
abbrev LanguageFamily (α : Type*) := GenLimit.Generic.LanguageFamily α
abbrev LanguageClass (α : Type*) := GenLimit.Generic.LanguageClass α
abbrev Stream (α : Type*) := GenLimit.Generic.Stream α
abbrev Generator (α : Type*) := GenLimit.Generic.Generator α

/-- The deterministic output made after observing the input at paper round
`t`.  The generator receives no target identifier or membership feedback. -/
def outputAfterInput {α : Type*}
    (gen : Generator α) (input : Stream α) : Stream α :=
  fun t => GenLimit.Generic.output gen input (t + 1)

/-- Dense-generation novelty over an arbitrary universe.  This is the exact
polymorphic analogue of `GenLimit.NovelGeneratesInLimit`. -/
def NovelGeneratesAfterInput {α : Type*}
    (input output : Stream α) (K : Language α) : Prop :=
  ∃ T, ∀ t, T ≤ t →
    output t ∈ K ∧
      output t ∉ GenLimit.Generic.sample input (t + 1) ∧
      ∀ s, s < t → output s ≠ output t

/-- The weaker eventual validity used by the impossibility clause: an output
must be in the target and absent from the sample through its own round, but it
need not be new relative to earlier outputs. -/
def SampleFreshGeneratesAfterInput {α : Type*}
    (input output : Stream α) (K : Language α) : Prop :=
  ∃ T, ∀ t, T ≤ t →
    output t ∈ K ∧ output t ∉ GenLimit.Generic.sample input (t + 1)

/-- Values first announced by the generator, with presenter-first same-round
ties, over an arbitrary universe. -/
def GeneratorFirstOn {α : Type*}
    (input output : Stream α) : Set α :=
  {x | ∃ t, output t = x ∧ ∀ s, s ≤ t → input s ≠ x}

/-- Rank-to-value map for the stipulated balanced order
`0, -1, 1, -2, 2, ...` on the integers. -/
def balanced : ℕ → ℤ
  | 0 => 0
  | n + 1 =>
      if n % 2 = 0 then -Int.ofNat (n / 2 + 1)
      else Int.ofNat (n / 2 + 1)

/-- Pull an integer language back to its set of ranks in the balanced order. -/
def balancedRanks (A : Language ℤ) : Set ℕ := balanced ⁻¹' A

/-- Relative lower density in balanced integer order, expressed through the
library's ambient-prefix density on the corresponding rank sets. -/
noncomputable def balancedRelativeLowerDensity
    (A K : Language ℤ) : ℝ :=
  GenLimit.PatientScope.relativeLowerDensity
    (balancedRanks A) (balancedRanks K)

/-- Every indexed countable family of infinite natural-number languages has
one presentation-dependent half-density generator at noise level `q`. -/
def CountableHalfDensity (q : ℕ) : Prop :=
  ∀ family : LanguageFamily ℕ,
    (∀ i, (family i).Infinite) →
      ∃ gen : Generator ℕ,
        ∀ i (input : Stream ℕ),
          GenLimit.Generic.InjectiveValueContaminatedPresentationAtMost
              input (family i) q →
            GenLimit.NovelGeneratesInLimit
                input (outputAfterInput gen input) (family i) ∧
              (1 / 2 : ℝ) ≤
                GenLimit.PatientScope.relativeLowerDensity
                  (GenLimit.GeneratorFirst
                    input (outputAfterInput gen input) ∩ family i)
                  (family i)

/-- One uncountable extensional family simultaneously has a quarter-density
generator at level `q` and defeats every semantic generator at level `q+1`. -/
def UncountableSeparation (q : ℕ) : Prop :=
  ∃ family : LanguageClass ℤ,
    ¬family.Countable ∧
      (∀ K ∈ family, K.Infinite) ∧
      (∃ gen : Generator ℤ,
        ∀ K ∈ family, ∀ input : Stream ℤ,
          GenLimit.Generic.InjectiveValueContaminatedPresentationAtMost
              input K q →
            NovelGeneratesAfterInput
                input (outputAfterInput gen input) K ∧
              (1 / 4 : ℝ) ≤
                balancedRelativeLowerDensity
                  (GeneratorFirstOn input (outputAfterInput gen input) ∩ K) K) ∧
      (∀ gen : Generator ℤ,
        ∃ K ∈ family, ∃ input : Stream ℤ,
          GenLimit.Generic.InjectiveValueContaminatedPresentationAtMost
              input K (q + 1) ∧
            ¬SampleFreshGeneratesAfterInput
              input (outputAfterInput gen input) K)

/-- The two quantified components of the exact Case 019 target. -/
def CountableClause : Prop := ∀ q, CountableHalfDensity q

def SeparationClause : Prop := ∀ q, UncountableSeparation q

/-- Exact Case 019 target.  The quarter is a witness constant, not an
optimality claim. -/
def MainClaim : Prop := CountableClause ∧ SeparationClause

end Stage3Case019
