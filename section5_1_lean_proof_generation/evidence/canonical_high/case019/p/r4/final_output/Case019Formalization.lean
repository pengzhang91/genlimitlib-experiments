import Helpers

open Stage3Case019
open Case019Formalization

/-- Checked partial result: every known infinite target has an always-valid,
sample-fresh, nonrepeating semantic generator. -/
theorem stage3_known_target_component {α : Type*} [DecidableEq α]
    (K : Language α) (hK : K.Infinite) (input : Stream α) :
    NovelGeneratesAfterInput input
      (outputAfterInput (freshGenerator K hK) input) K := by
  exact knownTarget_novel K hK input

/-- Checked partial result: the canonical separation witness has the required
extensional uncountability and member infinitude at every level. -/
theorem stage3_uncountable_witness_core :
    ∀ q : ℕ, ∃ family : LanguageClass ℤ,
      ¬family.Countable ∧ ∀ K ∈ family, K.Infinite := by
  exact witnessFamily_core
