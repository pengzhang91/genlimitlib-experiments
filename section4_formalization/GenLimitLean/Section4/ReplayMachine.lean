import Section4.ReplayConstruction
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod

/-! A finite Mealy transducer, with exact state cardinality, realizing the generator. -/
namespace Section4.Replay

open Set
open GenLimit.Replay

attribute [local instance] Classical.propDecidable

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem candidates_one (L : ι → Set α) (j : ι) (s : ℕ → α) :
    candidates L j (profile L (s 0)) s 1 = profile L (s 0) := by
  classical
  ext i
  rw [mem_candidates]
  constructor
  · exact And.left
  · intro hi
    refine ⟨hi, ?_⟩
    intro t ht _
    have ht0 : t = 0 := by omega
    simpa [ht0] using (mem_profile L (s 0) i).mp hi

theorem candidates_succ (L : ι → Set α) (j : ι) (P : Finset ι)
    (s : ℕ → α) (n : ℕ) :
    candidates L j P s (n + 1) =
      if s n ∈ L j then candidates L j P s n
      else candidates L j P s n ∩ profile L (s n) := by
  classical
  split_ifs with hx
  · ext i
    simp only [mem_candidates]
    constructor
    · rintro ⟨hi, hall⟩
      exact ⟨hi, fun t ht => hall t (by omega)⟩
    · rintro ⟨hi, hall⟩
      refine ⟨hi, ?_⟩
      intro t ht hout
      by_cases htn : t < n
      · exact hall t htn hout
      · have heq : t = n := by omega
        exact False.elim (hout (by simpa [heq] using hx))
  · ext i
    simp only [mem_candidates, Finset.mem_inter, mem_profile]
    constructor
    · rintro ⟨hi, hall⟩
      exact ⟨⟨hi, fun t ht => hall t (by omega)⟩, hall n (by omega) hx⟩
    · rintro ⟨⟨hi, hall⟩, hin⟩
      refine ⟨hi, ?_⟩
      intro t ht hout
      by_cases htn : t < n
      · exact hall t htn hout
      · have heq : t = n := by omega
        simpa [heq] using hin

abbrev MachineState (ι : Type*) := Option (ι × Finset ι)

def nextState (first : Finset ι → ι) : MachineState ι → Finset ι → MachineState ι
  | none, P => some (first P, P)
  | some (j, C), P => some (j, if j ∈ P then C else C ∩ P)

noncomputable def emit (L : ι → Set α) (first lower : Finset ι → ι) :
    MachineState ι → Finset ι → ι
  | none, P => first P
  | some (j, C), P => chosenOutput L lower j (if j ∈ P then C else C ∩ P)

def machineRun (first : Finset ι → ι) (input : ℕ → Finset ι) : ℕ → MachineState ι
  | 0 => none
  | n + 1 => nextState first (machineRun first input n) (input n)

theorem machineRun_succ (L : ι → Set α) (first : Finset ι → ι) (s : ℕ → α)
    (n : ℕ) :
    machineRun first (fun t => profile L (s t)) (n + 1) =
      some (first (profile L (s 0)),
        candidates L (first (profile L (s 0))) (profile L (s 0)) s (n + 1)) := by
  induction n with
  | zero => simp [machineRun, nextState, candidates_one]
  | succ n ih =>
    rw [machineRun, ih]
    simp only [nextState, mem_profile, candidates_succ]

theorem profile_machine_realizes (L : ι → Set α) (first lower : Finset ι → ι)
    (s : ℕ → α) (n : ℕ) :
    emit L first lower (machineRun first (fun t => profile L (s t)) n) (profile L (s n)) =
      properOutput (generator L first lower) s (n + 1) := by
  cases n with
  | zero => simp [machineRun, emit]
  | succ n =>
    rw [machineRun_succ]
    simp only [emit, mem_profile, generator_output_succ, Nat.succ_ne_zero, if_false,
      candidates_succ]

theorem machine_state_card :
    Fintype.card (MachineState ι) = 1 + Fintype.card ι * 2 ^ Fintype.card ι := by
  simp [MachineState, Fintype.card_option, Fintype.card_prod, Fintype.card_finset, Nat.add_comm]

end Section4.Replay
