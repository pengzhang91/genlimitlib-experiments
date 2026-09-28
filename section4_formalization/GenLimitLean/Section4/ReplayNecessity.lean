import Section4.ReplayCore
import GenLimit.Paper22_LanguageGenerationWithReplay.ProperSeparation
import Mathlib.Data.Set.Countable
import Mathlib.Data.Finset.Max

/-! Necessity of the finite proper-replay criterion in the original P22 model.
The proof constructs one complete stream for every target in a residual group,
then takes a common upper bound on their finitely many success times. -/

namespace Section4.Replay

open GenLimit.Replay

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Countable α]

theorem criterion_of_properlyGeneratable (L : ι → Set α)
    (hgen : ProperlyGeneratableInLimitWithReplay L) : Criterion L := by
  classical
  obtain ⟨gen, hgen⟩ := hgen
  intro x hx
  let j := gen 1 (fun _ => x)
  refine ⟨j, ?_⟩
  intro i hi
  have hxi : x ∈ L i := (mem_profile L x i).mp hi
  let U := L j ∪ residual L j i
  have hUi : L i ⊆ U := by
    intro y hy
    by_cases hj : y ∈ L j
    · exact Or.inl hj
    · exact Or.inr ⟨hy, hj⟩
  have hUne : U.Nonempty := ⟨x, hUi hxi⟩
  letI : Nonempty U := hUne.to_subtype
  obtain ⟨e, he⟩ := exists_surjective_nat U
  let stream : ℕ → α := fun n => match n with
    | 0 => x
    | n + 1 => (e n).val
  have hfirst : properOutput gen stream 1 = j := by
    apply congrArg (gen 1)
    funext k
    have hk : k = 0 := Fin.eq_zero k
    subst k
    rfl
  have hlegal : ∀ k ∈ group L j (profile L x) i,
      IsProperReplayEnumeration L gen k stream := by
    intro k hk
    obtain ⟨hkP, hkR⟩ := (mem_group L j (profile L x) i k).mp hk
    have hUk : L k ⊆ U := by
      intro y hy
      by_cases hj : y ∈ L j
      · exact Or.inl hj
      · exact Or.inr (hkR ▸ (show y ∈ residual L j k from ⟨hy, hj⟩))
    have hUki : U ⊆ L j ∪ L k := by
      intro y hy
      rcases hy with hy | hy
      · exact Or.inl hy
      · have hres : y ∈ residual L j k := hkR.symm ▸ hy
        exact Or.inr hres.1
    constructor
    · intro n
      cases n with
      | zero => exact Or.inl ((mem_profile L x k).mp hkP)
      | succ n =>
        rcases hUki (e n).property with hj | hk
        · exact Or.inr ⟨1, by omega, by omega, by simpa [hfirst] using hj⟩
        · exact Or.inl hk
    · intro y hy
      obtain ⟨n, hn⟩ := he ⟨y, hUk hy⟩
      exact ⟨n + 1, congrArg Subtype.val hn⟩
  have htimes : ∀ k, ∃ T, k ∈ group L j (profile L x) i →
      ∀ t, T ≤ t → ProperCorrectAt L gen k stream t := by
    intro k
    by_cases hk : k ∈ group L j (profile L x) i
    · obtain ⟨T, hT⟩ := hgen k stream (hlegal k hk)
      exact ⟨T, fun _ => hT⟩
    · exact ⟨0, fun h => (hk h).elim⟩
  choose T hT using htimes
  let t := Finset.univ.sup T
  refine ⟨properOutput gen stream t, ?_⟩
  intro k hk
  exact hT k hk t (Finset.le_sup (Finset.mem_univ k))

end Section4.Replay

#print axioms Section4.Replay.criterion_of_properlyGeneratable
