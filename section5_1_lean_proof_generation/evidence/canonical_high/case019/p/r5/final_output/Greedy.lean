import Stage3Model
import Mathlib

open Set

namespace Case019

private theorem exists_fresh_bounded {α : Type*} [DecidableEq α]
    (line : ℕ → α) (hline : Function.Injective line) (forbidden : Finset α) :
    ∃ n, n < forbidden.card + 1 ∧ line n ∉ forbidden := by
  classical
  by_contra hcontra
  have hall : ∀ n ∈ Finset.range (forbidden.card + 1), line n ∈ forbidden := by
    intro n hn
    by_contra hnmem
    apply hcontra
    exact ⟨n, Finset.mem_range.mp hn, hnmem⟩
  have hsub : (Finset.range (forbidden.card + 1)).image line ⊆ forbidden := by
    intro x hx
    simp only [Finset.mem_image] at hx
    obtain ⟨n, hn, rfl⟩ := hx
    exact hall n hn
  have hcard : forbidden.card + 1 ≤ forbidden.card := by
    calc
      forbidden.card + 1 = ((Finset.range (forbidden.card + 1)).image line).card := by
        rw [Finset.card_image_of_injective _ hline, Finset.card_range]
      _ ≤ forbidden.card := Finset.card_le_card hsub
  omega

theorem exists_fresh {α : Type*} [DecidableEq α]
    (line : ℕ → α) (hline : Function.Injective line) (forbidden : Finset α) :
    ∃ n, line n ∉ forbidden := by
  obtain ⟨n, _, hn⟩ := exists_fresh_bounded line hline forbidden
  exact ⟨n, hn⟩

noncomputable def freshRank {α : Type*} [DecidableEq α]
    (line : ℕ → α) (hline : Function.Injective line)
    (forbidden : Finset α) : ℕ :=
  Nat.find (exists_fresh line hline forbidden)

theorem freshRank_spec {α : Type*} [DecidableEq α]
    (line : ℕ → α) (hline : Function.Injective line) (forbidden : Finset α) :
    line (freshRank line hline forbidden) ∉ forbidden := by
  exact Nat.find_spec (exists_fresh line hline forbidden)

theorem freshRank_le_card {α : Type*} [DecidableEq α]
    (line : ℕ → α) (hline : Function.Injective line) (forbidden : Finset α) :
    freshRank line hline forbidden ≤ forbidden.card := by
  unfold freshRank
  obtain ⟨n, hn, hnmem⟩ := exists_fresh_bounded line hline forbidden
  have hmin : Nat.find (exists_fresh line hline forbidden) ≤ n :=
    Nat.find_min' (exists_fresh line hline forbidden) hnmem
  omega

noncomputable def greedyOutputs {α : Type*} [DecidableEq α]
    (line : ℕ → α) (hline : Function.Injective line) :
    (t : ℕ) → (Fin t → α) → (Fin t → α)
  | 0, _ => Fin.elim0
  | t + 1, history =>
      let previous := greedyOutputs line hline t (fun i => history i.castSucc)
      let forbidden := GenLimit.Generic.sequenceSample history ∪ Finset.univ.image previous
      let next := line (freshRank line hline forbidden)
      Fin.lastCases next previous

noncomputable def greedyGenerator {α : Type*} [DecidableEq α]
    (line : ℕ → α) (hline : Function.Injective line) : Stage3Case019.Generator α :=
  fun t history =>
    match t with
    | 0 => line 0
    | s + 1 => greedyOutputs line hline (s + 1) history (Fin.last s)

@[simp] theorem greedyOutputs_last {α : Type*} [DecidableEq α]
    (line : ℕ → α) (hline : Function.Injective line)
    (t : ℕ) (history : Fin (t + 1) → α) :
    greedyOutputs line hline (t + 1) history (Fin.last t) =
      line (freshRank line hline
        (GenLimit.Generic.sequenceSample history ∪
          Finset.univ.image
            (greedyOutputs line hline t (fun i => history i.castSucc)))) := by
  simp [greedyOutputs]

@[simp] theorem greedyGenerator_succ {α : Type*} [DecidableEq α]
    (line : ℕ → α) (hline : Function.Injective line)
    (t : ℕ) (history : Fin (t + 1) → α) :
    greedyGenerator line hline (t + 1) history =
      greedyOutputs line hline (t + 1) history (Fin.last t) := by
  simp [greedyGenerator]

end Case019

namespace Case019

@[simp] theorem greedyOutputs_castSucc {α : Type*} [DecidableEq α]
    (line : ℕ → α) (hline : Function.Injective line)
    (t : ℕ) (history : Fin (t + 1) → α) (i : Fin t) :
    greedyOutputs line hline (t + 1) history i.castSucc =
      greedyOutputs line hline t (fun j => history j.castSucc) i := by
  simp [greedyOutputs]

theorem greedyOutputs_prefix {α : Type*} [DecidableEq α]
    (line : ℕ → α) (hline : Function.Injective line)
    {s t : ℕ} (hst : s ≤ t) (history : Fin t → α) (i : Fin s) :
    greedyOutputs line hline t history ⟨i, Nat.lt_of_lt_of_le i.isLt hst⟩ =
      greedyOutputs line hline s (fun j => history ⟨j, Nat.lt_of_lt_of_le j.isLt hst⟩) i := by
  induction t, hst using Nat.le_induction with
  | base => rfl
  | succ t hst ih =>
      let k : Fin t := ⟨i, Nat.lt_of_lt_of_le i.isLt hst⟩
      have hi : (⟨i, Nat.lt_of_lt_of_le i.isLt (Nat.le.step hst)⟩ : Fin (t + 1)) =
          k.castSucc := Fin.ext rfl
      rw [hi, greedyOutputs_castSucc]
      simpa [k] using ih (fun j => history j.castSucc)

theorem greedy_last_not_sample {α : Type*} [DecidableEq α]
    (line : ℕ → α) (hline : Function.Injective line)
    (t : ℕ) (history : Fin (t + 1) → α) :
    greedyOutputs line hline (t + 1) history (Fin.last t) ∉
      GenLimit.Generic.sequenceSample history := by
  rw [greedyOutputs_last]
  have hfresh := freshRank_spec line hline
    (GenLimit.Generic.sequenceSample history ∪
      Finset.univ.image (greedyOutputs line hline t (fun i => history i.castSucc)))
  exact fun hmem => hfresh (Finset.mem_union_left _ hmem)

theorem greedy_last_ne_previous {α : Type*} [DecidableEq α]
    (line : ℕ → α) (hline : Function.Injective line)
    (t : ℕ) (history : Fin (t + 1) → α) (i : Fin t) :
    greedyOutputs line hline t (fun j => history j.castSucc) i ≠
      greedyOutputs line hline (t + 1) history (Fin.last t) := by
  rw [greedyOutputs_last]
  intro heq
  have hfresh := freshRank_spec line hline
    (GenLimit.Generic.sequenceSample history ∪
      Finset.univ.image (greedyOutputs line hline t (fun j => history j.castSucc)))
  apply hfresh
  apply Finset.mem_union_right
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, heq⟩

theorem greedy_last_rank_bound {α : Type*} [DecidableEq α]
    (line : ℕ → α) (hline : Function.Injective line)
    (t : ℕ) (history : Fin (t + 1) → α) :
    ∃ n ≤ 2 * t + 1,
      greedyOutputs line hline (t + 1) history (Fin.last t) = line n := by
  classical
  let previous := greedyOutputs line hline t (fun i => history i.castSucc)
  let forbidden := GenLimit.Generic.sequenceSample history ∪ Finset.univ.image previous
  have hsample : (GenLimit.Generic.sequenceSample history).card ≤ t + 1 := by
    calc
      (GenLimit.Generic.sequenceSample history).card =
          ((Finset.univ : Finset (Fin (t + 1))).image history).card := by
            congr 1
            ext x
            simp [GenLimit.Generic.sequenceSample]
      _ ≤ (Finset.univ : Finset (Fin (t + 1))).card := Finset.card_image_le
      _ = t + 1 := by simp
  have hprevious : (Finset.univ.image previous).card ≤ t := by
    exact Finset.card_image_le.trans (by simp)
  refine ⟨freshRank line hline forbidden, ?_, ?_⟩
  · calc
      freshRank line hline forbidden ≤ forbidden.card := freshRank_le_card line hline forbidden
      _ ≤ (GenLimit.Generic.sequenceSample history).card +
          (Finset.univ.image previous).card := Finset.card_union_le _ _
      _ ≤ (t + 1) + t := Nat.add_le_add hsample hprevious
      _ = 2 * t + 1 := by omega
  · simp [previous, forbidden, greedyOutputs]

theorem outputAfterInput_greedy {α : Type*} [DecidableEq α]
    (line : ℕ → α) (hline : Function.Injective line)
    (input : Stage3Case019.Stream α) (t : ℕ) :
    Stage3Case019.outputAfterInput (greedyGenerator line hline) input t =
      greedyOutputs line hline (t + 1) (fun i => input i) (Fin.last t) := by
  simp [Stage3Case019.outputAfterInput, GenLimit.Generic.output]

theorem greedy_output_mem_line {α : Type*} [DecidableEq α]
    (line : ℕ → α) (hline : Function.Injective line)
    (input : Stage3Case019.Stream α) (t : ℕ) :
    Stage3Case019.outputAfterInput (greedyGenerator line hline) input t ∈ Set.range line := by
  rw [outputAfterInput_greedy]
  obtain ⟨n, _, hn⟩ := greedy_last_rank_bound line hline t (fun i => input i)
  exact ⟨n, hn.symm⟩

theorem sequenceSample_eq_sample {α : Type*} [DecidableEq α]
    (input : Stage3Case019.Stream α) (t : ℕ) :
    GenLimit.Generic.sequenceSample (fun i : Fin t => input i) =
      GenLimit.Generic.sample input t := by
  ext x
  constructor
  · intro hx
    simp only [GenLimit.Generic.sequenceSample, Finset.mem_image, Finset.mem_univ,
      true_and] at hx
    obtain ⟨i, hi⟩ := hx
    simp only [GenLimit.Generic.sample, Finset.mem_image, Finset.mem_range]
    exact ⟨i, i.isLt, hi⟩
  · intro hx
    simp only [GenLimit.Generic.sample, Finset.mem_image, Finset.mem_range] at hx
    obtain ⟨i, hit, hi⟩ := hx
    simp only [GenLimit.Generic.sequenceSample, Finset.mem_image, Finset.mem_univ,
      true_and]
    exact ⟨⟨i, hit⟩, hi⟩

theorem greedy_output_not_sample {α : Type*} [DecidableEq α]
    (line : ℕ → α) (hline : Function.Injective line)
    (input : Stage3Case019.Stream α) (t : ℕ) :
    Stage3Case019.outputAfterInput (greedyGenerator line hline) input t ∉
      GenLimit.Generic.sample input (t + 1) := by
  rw [outputAfterInput_greedy, ← sequenceSample_eq_sample]
  exact greedy_last_not_sample line hline t (fun i => input i)

theorem greedy_output_ne_of_lt {α : Type*} [DecidableEq α]
    (line : ℕ → α) (hline : Function.Injective line)
    (input : Stage3Case019.Stream α) {s t : ℕ} (hst : s < t) :
    Stage3Case019.outputAfterInput (greedyGenerator line hline) input s ≠
      Stage3Case019.outputAfterInput (greedyGenerator line hline) input t := by
  rw [outputAfterInput_greedy, outputAfterInput_greedy]
  let history : Fin (t + 1) → α := fun i => input i
  have hpref := greedyOutputs_prefix line hline (s := s + 1) (t := t)
    (by omega) (fun i : Fin t => history i.castSucc) (Fin.last s)
  have hne := greedy_last_ne_previous line hline t history
    ⟨s, by omega⟩
  intro heq
  apply hne
  exact hpref.trans heq

theorem greedy_output_injective {α : Type*} [DecidableEq α]
    (line : ℕ → α) (hline : Function.Injective line)
    (input : Stage3Case019.Stream α) :
    Function.Injective (Stage3Case019.outputAfterInput (greedyGenerator line hline) input) := by
  intro s t heq
  rcases lt_trichotomy s t with hlt | heqst | hgt
  · exact False.elim (greedy_output_ne_of_lt line hline input hlt heq)
  · exact heqst
  · exact False.elim (greedy_output_ne_of_lt line hline input hgt heq.symm)

end Case019

namespace Case019

 theorem greedy_novel_after_input {α : Type*} [DecidableEq α]
    (line : ℕ → α) (hline : Function.Injective line)
    (input : Stage3Case019.Stream α) (K : Stage3Case019.Language α)
    (hK : Set.range line ⊆ K) :
    Stage3Case019.NovelGeneratesAfterInput input
      (Stage3Case019.outputAfterInput (greedyGenerator line hline) input) K := by
  refine ⟨0, ?_⟩
  intro t _
  refine ⟨hK (greedy_output_mem_line line hline input t),
    greedy_output_not_sample line hline input t, ?_⟩
  intro s hst
  exact greedy_output_ne_of_lt line hline input hst

 theorem greedy_novel_nat
    (line : ℕ → ℕ) (hline : Function.Injective line)
    (input : Stage3Case019.Stream ℕ) (K : Stage3Case019.Language ℕ)
    (hK : Set.range line ⊆ K) :
    GenLimit.NovelGeneratesInLimit input
      (Stage3Case019.outputAfterInput (greedyGenerator line hline) input) K := by
  refine ⟨0, ?_⟩
  intro t _
  have hfresh := greedy_output_not_sample line hline input t
  refine ⟨hK (greedy_output_mem_line line hline input t), ?_, ?_⟩
  · simpa [GenLimit.Generic.sample, GenLimit.sample] using hfresh
  · intro s hst
    exact greedy_output_ne_of_lt line hline input hst

 theorem greedy_output_rank_bound {α : Type*} [DecidableEq α]
    (line : ℕ → α) (hline : Function.Injective line)
    (input : Stage3Case019.Stream α) (t : ℕ) :
    ∃ n ≤ 2 * t + 1,
      Stage3Case019.outputAfterInput (greedyGenerator line hline) input t = line n := by
  rw [outputAfterInput_greedy]
  exact greedy_last_rank_bound line hline t (fun i => input i)

end Case019
