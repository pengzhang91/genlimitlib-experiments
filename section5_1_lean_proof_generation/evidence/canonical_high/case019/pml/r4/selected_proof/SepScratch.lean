import Stage3Model
import GenLimit.Paper39_DenseGeneration.Patient.Main
import GenLimit.Paper12_NoiseLossAndFeedback.FiniteNoiseSeparation
import GenLimit.Paper10_UnionClosednessOfLanguageGeneration.Cardinality
import Mathlib.Logic.Equiv.Finset

open Stage3Case019
open GenLimit
open Filter

namespace SepScratch

noncomputable def decodedFinset (i : ℕ) : Finset ℕ :=
  (Encodable.decode i : Option (Finset ℕ)).getD ∅

noncomputable def cofiniteAnchorFamily : GenLimit.LanguageFamily :=
  fun i => {n | n = 0 ∨ n ∉ decodedFinset i}

lemma cofiniteAnchorFamily_infinite (i : ℕ) :
    (cofiniteAnchorFamily i).Infinite := by
  apply Set.Infinite.mono (s := (decodedFinset i : Set ℕ)ᶜ)
  · exact (decodedFinset i).finite_toSet.compl
  · intro n hn
    exact Or.inr hn

noncomputable def cofiniteAnchorOracle : OracleFamily where
  language := cofiniteAnchorFamily
  infinite' := cofiniteAnchorFamily_infinite
  query i n := by classical exact decide (n ∈ cofiniteAnchorFamily i)
  query_spec i n := by classical simp

lemma exists_cofiniteAnchor_index {S : Set ℕ}
    (hzero : 0 ∈ S) (hfinite : Sᶜ.Finite) :
    ∃ i, cofiniteAnchorFamily i = S := by
  classical
  let F : Finset ℕ := hfinite.toFinset
  let i := Encodable.encode F
  refine ⟨i, ?_⟩
  have hdecode : decodedFinset i = F := by
    simp [decodedFinset, i, Encodable.encodek]
  ext n
  simp only [cofiniteAnchorFamily, Set.mem_setOf_eq, hdecode]
  constructor
  · intro hn
    rcases hn with rfl | hn
    · exact hzero
    · by_contra hnot
      exact hn (by simpa [F] using hnot)
  · intro hn
    by_cases hn0 : n = 0
    · exact Or.inl hn0
    · exact Or.inr (by
        intro hnF
        have : n ∈ Sᶜ := by simpa [F] using hnF
        exact this hn)

abbrev negCode := GenLimit.UnionClosedness.negativeCode

def positiveCode0 (n : ℕ) : ℤ := Int.ofNat n

def positiveProject (z : ℤ) : ℕ := z.toNat

def negativeProject (z : ℤ) : ℕ :=
  if z < 0 then z.natAbs - 1 else 0

lemma positiveProject_positiveCode0 (n : ℕ) :
    positiveProject (positiveCode0 n) = n := by
  simp [positiveProject, positiveCode0]

lemma negativeProject_negCode (n : ℕ) :
    negativeProject (negCode n) = n := by
  simp [negativeProject, negCode, GenLimit.UnionClosedness.negativeCode]

lemma positiveCode0_injective : Function.Injective positiveCode0 := by
  intro a b h
  exact Int.ofNat_inj.mp h

lemma positiveCode0_nonnegative (n : ℕ) : (0 : ℤ) ≤ positiveCode0 n := by
  simp [positiveCode0]

lemma negCode_negative (n : ℕ) : negCode n < 0 :=
  GenLimit.UnionClosedness.negativeCode_mem n

noncomputable def sidePatientGenerator (q : ℕ) : Generator ℤ :=
  fun n xs =>
    if GenLimit.NoiseLossFeedback.omissionMarkerFinset q ⊆
        GenLimit.Generic.sequenceSample xs then
      positiveCode0 (Case019.patientGenerator cofiniteAnchorOracle n
        (fun k => positiveProject (xs k)))
    else
      negCode (Case019.patientGenerator cofiniteAnchorOracle n
        (fun k => negativeProject (xs k)))

lemma sidePatientGenerator_positive_output
    {q t : ℕ} {input : Stream ℤ}
    (hmarkers : GenLimit.NoiseLossFeedback.omissionMarkerFinset q ⊆
      GenLimit.Generic.sample input (t + 1)) :
    outputAfterInput (sidePatientGenerator q) input t =
      positiveCode0 (PatientMachine.output cofiniteAnchorOracle
        (fun s => positiveProject (input s)) t) := by
  unfold outputAfterInput GenLimit.Generic.output sidePatientGenerator
  have hsample : GenLimit.Generic.sequenceSample
      (fun k : Fin (t + 1) => input k) =
      GenLimit.Generic.sample input (t + 1) :=
    GenLimit.Generic.sequenceSample_prefix input (t + 1)
  rw [if_pos (by simpa [hsample] using hmarkers)]
  rw [Case019.patientGenerator_output]

lemma sidePatientGenerator_negative_output
    {q t : ℕ} {input : Stream ℤ}
    (hmarkers : ¬ GenLimit.NoiseLossFeedback.omissionMarkerFinset q ⊆
      GenLimit.Generic.sample input (t + 1)) :
    outputAfterInput (sidePatientGenerator q) input t =
      negCode (PatientMachine.output cofiniteAnchorOracle
        (fun s => negativeProject (input s)) t) := by
  unfold outputAfterInput GenLimit.Generic.output sidePatientGenerator
  have hsample : GenLimit.Generic.sequenceSample
      (fun k : Fin (t + 1) => input k) =
      GenLimit.Generic.sample input (t + 1) :=
    GenLimit.Generic.sequenceSample_prefix input (t + 1)
  rw [if_neg (by simpa [hsample] using hmarkers)]
  rw [Case019.patientGenerator_output]

end SepScratch
