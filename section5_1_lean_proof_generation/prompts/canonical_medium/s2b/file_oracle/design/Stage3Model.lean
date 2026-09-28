import Mathlib.Data.Set.Countable
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Range
import Mathlib.Data.Real.Archimedean
import Mathlib.Order.LiminfLimsup
import GenLimit.Core.OrderedDensity

/-!
S2-B specification.
Only definitions, interfaces, and the target proposition are supplied here.
There is no diagonal construction or mathematical supporting theorem.
-/

namespace Stage3S2B

abbrev Language := Set ℕ
abbrev LanguageClass := Set Language
abbrev Stream := ℕ → ℕ

def core : Language := Set.range (fun k : ℕ => 2 ^ k)
def ordinary : Language := coreᶜ
def targetClass : LanguageClass :=
  {K | ∃ A : Language, A ⊆ ordinary ∧ K = core ∪ A}

structure FeedbackGenerator where
  query : (t : ℕ) → (Fin (t + 1) → ℕ) →
    (Fin t → Option Bool) → Option ℕ
  output : (t : ℕ) → (Fin (t + 1) → ℕ) →
    (Fin (t + 1) → Option Bool) → ℕ

structure Transcript where
  presentation : Stream
  query : ℕ → Option ℕ
  answer : ℕ → Option Bool
  output : Stream

structure CausalPresenter where
  next : (t : ℕ) → (Fin t → ℕ) → (Fin t → Option ℕ) →
    (Fin t → Option Bool) → (Fin t → ℕ) → ℕ

def PresentedBy (presenter : CausalPresenter) (tr : Transcript) : Prop :=
  ∀ t, tr.presentation t = presenter.next t
    (fun i => tr.presentation i) (fun i => tr.query i)
    (fun i => tr.answer i) (fun i => tr.output i)

noncomputable def membershipAnswer (K : Language) (z : ℕ) : Bool := by
  classical
  exact decide (z ∈ K)

def FollowsProtocol (gen : FeedbackGenerator) (K : Language)
    (tr : Transcript) : Prop :=
  ∀ t,
    tr.query t = gen.query t
      (fun i => tr.presentation i) (fun i => tr.answer i) ∧
    tr.answer t = (match tr.query t with
      | none => none
      | some z => some (membershipAnswer K z)) ∧
    tr.output t = gen.output t
      (fun i => tr.presentation i) (fun i => tr.answer i)

def observedThrough (x : Stream) (t : ℕ) : Set ℕ :=
  {z | ∃ s, s ≤ t ∧ x s = z}

def Clean (x : Stream) (K : Language) : Prop := ∀ t, x t ∈ K
def Complete (x : Stream) (K : Language) : Prop :=
  ∀ z, z ∈ K → ∃ t, x t = z

/-- Equivalent to first-output time strictly before first-presentation time:
an output occurrence before any presentation exists iff the first one is. -/
def scored (K : Language) (x y : Stream) : Language :=
  {z | z ∈ K ∧ ∃ t, y t = z ∧ z ∉ observedThrough x t}

abbrev OrderedLanguage := GenLimit.KleinbergWei.OrderedLanguage

def InheritsAmbientOrder (K : OrderedLanguage) : Prop := StrictMono K.enumeration

def UniformlyGeneratableWithoutSamples : Prop :=
  ∃ f : Stream, Function.Injective f ∧
    ∃ T : ℕ, ∀ K, K ∈ targetClass → ∀ t, T ≤ t → f t ∈ K

def UniversallyEventuallyValidFresh (gen : FeedbackGenerator) : Prop :=
  ∀ K, K ∈ targetClass → ∀ tr : Transcript,
    FollowsProtocol gen K tr → Clean tr.presentation K →
    Function.Injective tr.presentation → Complete tr.presentation K →
    ∃ T : ℕ, ∀ t, T ≤ t →
      tr.output t ∈ K ∧ tr.output t ∉ observedThrough tr.presentation t

def FaithfulNegativeWitness (gen : FeedbackGenerator) (K : Language)
    (presenter : CausalPresenter) (tr : Transcript) (orderedK : OrderedLanguage) : Prop :=
  orderedK.carrier = K ∧ InheritsAmbientOrder orderedK ∧
  PresentedBy presenter tr ∧ FollowsProtocol gen K tr ∧
  Clean tr.presentation K ∧ Function.Injective tr.presentation ∧
  Complete tr.presentation K ∧
  orderedK.upperDensity (scored K tr.presentation tr.output) = 0

def NegativeClaim : Prop :=
  ∀ gen : FeedbackGenerator, UniversallyEventuallyValidFresh gen →
    ∃ K : Language, K ∈ targetClass ∧
      ∃ presenter : CausalPresenter, ∃ tr : Transcript,
        ∃ orderedK : OrderedLanguage,
          FaithfulNegativeWitness gen K presenter tr orderedK

/-- Required final proposition; uncountability is explicitly included. -/
def MainClaim : Prop :=
  ¬ targetClass.Countable ∧ UniformlyGeneratableWithoutSamples ∧ NegativeClaim

end Stage3S2B
