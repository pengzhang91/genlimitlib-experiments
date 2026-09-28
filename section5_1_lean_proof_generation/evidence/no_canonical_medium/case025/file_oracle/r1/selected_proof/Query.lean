import Stage3Model
import GenLimit.Paper39_DenseGeneration.Patient.Main
import Mathlib.Logic.Encodable.Basic
open GenLimit
noncomputable section
private def decodedFinset (n : ℕ) : Finset ℕ :=
  ((Encodable.decode n : Option (List ℕ)).getD []).toFinset
example (F : Set ℕ) (hF : F.Finite) :
    decodedFinset (Encodable.encode hF.toFinset.toList) = hF.toFinset := by
  simp [decodedFinset]
example (i c : ℕ) : (Nat.pair i c).unpair.1 = i := by simp
example (i c : ℕ) : (Nat.pair i c).unpair.2 = c := by simp
