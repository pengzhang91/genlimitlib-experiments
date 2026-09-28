import PatientBridge

open Stage3Case025

namespace Stage3Case025

open GenLimit
open PatientBridge

theorem positivePresentationHalfDensity :
    PositivePresentationHalfDensity := by
  intro family hInfinite
  let O := oracleOfFamily family hInfinite
  refine ⟨onlineGenerator O, ?_⟩
  intro i input hPresents
  let output : Stream := GenLimit.PatientMachine.output O input
  refine ⟨output, follows_onlineGenerator O input, ?_, ?_⟩
  · obtain ⟨hNovel, _⟩ :=
      GenLimit.PatientMachine.patientScope_generation_and_lowerDensity
        O input (z := i) hPresents
    obtain ⟨T, hT⟩ := hNovel
    refine ⟨T, ?_⟩
    intro t ht
    obtain ⟨hmem, hfresh, hinj⟩ := hT t ht
    refine ⟨hmem, ?_, hinj⟩
    rw [GenLimit.mem_sample_iff]
    rintro ⟨s, hs, heq⟩
    exact hfresh s (Nat.lt_succ_iff.mp hs) heq
  · obtain ⟨_, hDensity⟩ :=
      GenLimit.PatientMachine.patientScope_generation_and_lowerDensity
        O input (z := i) hPresents
    exact hDensity

end Stage3Case025
