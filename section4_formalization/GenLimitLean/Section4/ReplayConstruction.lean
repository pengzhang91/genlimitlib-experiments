import Section4.ReplayCore
import GenLimit.Paper22_LanguageGenerationWithReplay.ProperSeparation

/-! Explicit full-history proper generator implementing the residual construction. -/
namespace Section4.Replay

open Set
open GenLimit.Replay

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

noncomputable def defaultIndex : ι := Classical.choice inferInstance

noncomputable def firstChoice (L : ι → Set α) (P : Finset ι) : ι := by
  classical
  exact if h : ∃ j, GoodFirst L P j then h.choose else defaultIndex

theorem firstChoice_spec (L : ι → Set α) (hc : Criterion L) (x : α)
    (hx : ∃ i, x ∈ L i) : GoodFirst L (profile L x) (firstChoice L (profile L x)) := by
  classical
  have h := hc x hx
  simp only [firstChoice, dif_pos h]
  exact h.choose_spec

noncomputable def lowerChoice (L : ι → Set α) (E : Finset ι) : ι := by
  classical
  exact if h : ∃ i, CommonLower L E i then h.choose else defaultIndex

def LowerSpec (L : ι → Set α) (lower : Finset ι → ι) : Prop :=
  ∀ E, (∃ i, CommonLower L E i) → CommonLower L E (lower E)

theorem lowerChoice_spec (L : ι → Set α) : LowerSpec L (lowerChoice L) := by
  classical
  intro E h
  simp only [lowerChoice, dif_pos h]
  exact h.choose_spec

noncomputable def candidates (L : ι → Set α) (j : ι) (P : Finset ι)
    (s : ℕ → α) (n : ℕ) : Finset ι := by
  classical
  exact P.filter (fun i => ∀ t < n, s t ∉ L j → s t ∈ L i)

@[simp] theorem mem_candidates (L : ι → Set α) (j : ι) (P : Finset ι)
    (s : ℕ → α) (n : ℕ) (i : ι) :
    i ∈ candidates L j P s n ↔ i ∈ P ∧ ∀ t < n, s t ∉ L j → s t ∈ L i := by
  classical
  simp [candidates]

theorem candidates_subset (L : ι → Set α) (j : ι) (P : Finset ι)
    (s : ℕ → α) (n : ℕ) : candidates L j P s n ⊆ P := by
  intro i hi
  exact (mem_candidates L j P s n i).mp hi |>.1

theorem candidates_antitone (L : ι → Set α) (j : ι) (P : Finset ι)
    (s : ℕ → α) : Antitone (candidates L j P s) := by
  intro m n hmn i hi
  rcases (mem_candidates L j P s n i).mp hi with ⟨hiP, hi⟩
  exact (mem_candidates L j P s m i).mpr ⟨hiP, fun t ht => hi t (lt_of_lt_of_le ht hmn)⟩

theorem candidates_group_eq (L : ι → Set α) (j : ι) (P : Finset ι)
    (s : ℕ → α) (n : ℕ) {i : ι} (hi : i ∈ candidates L j P s n) :
    group L j (candidates L j P s n) i = group L j P i := by
  classical
  ext k
  simp only [mem_group]
  constructor
  · intro hk
    exact ⟨candidates_subset L j P s n hk.1, hk.2⟩
  · rintro ⟨hkP, heq⟩
    refine ⟨?_, heq⟩
    rw [mem_candidates]
    refine ⟨hkP, ?_⟩
    intro t ht hx
    exact (residual_eq_mem_iff L j heq hx).mpr ((mem_candidates L j P s n i).mp hi |>.2 t ht hx)

def LeastCandidate (L : ι → Set α) (j : ι) (C : Finset ι) (i : ι) : Prop :=
  i ∈ C ∧ ∀ k ∈ C, residual L j i ⊆ residual L j k

noncomputable def chosenOutput (L : ι → Set α) (lower : Finset ι → ι)
    (j : ι) (C : Finset ι) : ι := by
  classical
  exact if h : ∃ i, LeastCandidate L j C i then
    lower (group L j C h.choose) else j

theorem chosenOutput_contained (L : ι → Set α) (lower : Finset ι → ι)
    (hlower : LowerSpec L lower) (j : ι) (P : Finset ι)
    (hgood : GoodFirst L P j) (s : ℕ → α) (n : ℕ)
    {target : ι} (htarget : target ∈ candidates L j P s n) :
    L (chosenOutput L lower j (candidates L j P s n)) ⊆ L j ∪ L target := by
  classical
  unfold chosenOutput
  split_ifs with h
  · let k := h.choose
    have hk : LeastCandidate L j (candidates L j P s n) k := h.choose_spec
    have hl := hlower (group L j P k) (hgood k (candidates_subset L j P s n hk.1))
    rw [candidates_group_eq L j P s n hk.1]
    intro x hx
    have hxk := hl k (self_mem_group L j (candidates_subset L j P s n hk.1)) hx
    by_cases hxj : x ∈ L j
    · exact Or.inl hxj
    · exact Or.inr ((hk.2 target htarget) ⟨hxk, hxj⟩).1
  · exact Set.subset_union_left

theorem chosenOutput_eq_of_least (L : ι → Set α) (lower : Finset ι → ι)
    (j : ι) (P : Finset ι) (s : ℕ → α) (n : ℕ) {target : ι}
    (htarget : LeastCandidate L j (candidates L j P s n) target) :
    chosenOutput L lower j (candidates L j P s n) = lower (group L j P target) := by
  classical
  have h : ∃ i, LeastCandidate L j (candidates L j P s n) i := ⟨target, htarget⟩
  rw [chosenOutput, dif_pos h]
  have hk := h.choose_spec
  have heq : residual L j h.choose = residual L j target :=
    Set.Subset.antisymm (hk.2 target htarget.1) (htarget.2 h.choose hk.1)
  rw [group_eq_of_residual_eq L j _ heq, candidates_group_eq L j P s n htarget.1]

/-- Extend a finite tuple by repeating its first point. Only the tuple prefix is used. -/
def tupleStream {n : ℕ} (xs : Fin (n + 1) → α) : ℕ → α :=
  fun t => if h : t < n + 1 then xs ⟨t, h⟩ else xs ⟨0, Nat.zero_lt_succ n⟩

@[simp] theorem tupleStream_prefix {n : ℕ} (xs : Fin (n + 1) → α)
    {t : ℕ} (ht : t < n + 1) : tupleStream xs t = xs ⟨t, ht⟩ := by
  simp [tupleStream, ht]

/-- This is literally P22's finite-history proper generator interface. -/
noncomputable def generator (L : ι → Set α) (first lower : Finset ι → ι) :
    GenLimit.Replay.ProperGenerator ι α :=
  fun n => match n with
  | 0 => fun _ => defaultIndex
  | n + 1 => fun xs =>
      let P := profile L (xs ⟨0, Nat.zero_lt_succ n⟩)
      let j := first P
      if n = 0 then j else chosenOutput L lower j (candidates L j P (tupleStream xs) (n + 1))

theorem candidates_tupleStream (L : ι → Set α) (j : ι) (P : Finset ι)
    (s : ℕ → α) (n : ℕ) :
    candidates L j P (tupleStream (fun k : Fin (n + 1) => s k)) (n + 1) =
      candidates L j P s (n + 1) := by
  classical
  ext i
  simp only [mem_candidates]
  constructor <;> rintro ⟨hi, hall⟩ <;> refine ⟨hi, ?_⟩
  · intro t ht
    simpa only [tupleStream_prefix _ ht] using hall t ht
  · intro t ht
    simpa only [tupleStream_prefix _ ht] using hall t ht

@[simp] theorem generator_output_succ (L : ι → Set α) (first lower : Finset ι → ι)
    (s : ℕ → α) (n : ℕ) :
    properOutput (generator L first lower) s (n + 1) =
      if n = 0 then first (profile L (s 0)) else
      chosenOutput L lower (first (profile L (s 0)))
        (candidates L (first (profile L (s 0))) (profile L (s 0)) s (n + 1)) := by
  simp only [properOutput, generator, candidates_tupleStream]

@[simp] theorem generator_output_one (L : ι → Set α) (first lower : Finset ι → ι)
    (s : ℕ → α) :
    properOutput (generator L first lower) s 1 = first (profile L (s 0)) := by
  simpa using generator_output_succ L first lower s 0

end Section4.Replay
