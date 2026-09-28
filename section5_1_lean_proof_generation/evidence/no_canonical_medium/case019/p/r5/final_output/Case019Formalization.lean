import Stage3Model
import Mathlib.Tactic

open Stage3Case019

namespace Stage3Case019Partial

lemma tail_injective_of_novel {α : Type*}
    {input output : Stream α} {K : Language α} {T : ℕ}
    (hNovel : ∀ t, T ≤ t →
      output t ∈ K ∧
        output t ∉ GenLimit.Generic.sample input (t + 1) ∧
        ∀ s, s < t → output s ≠ output t) :
    Function.Injective (fun n => output (T + n)) := by
  intro a b hab
  rcases lt_trichotomy a b with hablt | rfl | hbalt
  · have hne := (hNovel (T + b) (by omega)).2.2 (T + a) (by omega)
    exact False.elim (hne hab)
  · rfl
  · have hne := (hNovel (T + a) (by omega)).2.2 (T + b) (by omega)
    exact False.elim (hne hab.symm)

lemma novel_of_finite_range_difference {α : Type*}
    {input output : Stream α} {R K : Language α} {q : ℕ}
    (hDiff : GenLimit.Generic.SetDifferenceAtMost R K q)
    (hNovel : NovelGeneratesAfterInput input output R) :
    NovelGeneratesAfterInput input output K := by
  rcases hDiff with ⟨contaminants, hcontaminants, hcard⟩
  rcases hNovel with ⟨T, hT⟩
  have hTailInjective : Function.Injective (fun n => output (T + n)) :=
    tail_injective_of_novel hT
  let badTimes : Set ℕ :=
    (fun n => output (T + n)) ⁻¹' (contaminants : Set α)
  have hBadFinite : badTimes.Finite := by
    apply Set.Finite.preimage
    · exact hTailInjective.injOn
    · exact contaminants.finite_toSet
  rcases hBadFinite.bddAbove with ⟨B, hB⟩
  refine ⟨T + B + 1, ?_⟩
  intro t ht
  have hTt : T ≤ t := by omega
  rcases hT t hTt with ⟨htR, htSample, htFresh⟩
  refine ⟨?_, htSample, htFresh⟩
  by_contra htK
  have htContaminant : output t ∈ (contaminants : Set α) := by
    rw [hcontaminants]
    exact ⟨htR, htK⟩
  let n := t - T
  have htn : T + n = t := by
    dsimp [n]
    omega
  have hnBad : n ∈ badTimes := by
    change output (T + n) ∈ (contaminants : Set α)
    rwa [htn]
  have hnB : n ≤ B := hB hnBad
  have hBn : B < n := by
    dsimp [n]
    omega
  omega

lemma contaminated_presentation_eventually_removes_noise {α : Type*}
    {input output : Stream α} {K : Language α} {q : ℕ}
    (hPresentation :
      GenLimit.Generic.InjectiveValueContaminatedPresentationAtMost input K q)
    (hNovelRange :
      NovelGeneratesAfterInput input output (Set.range input)) :
    NovelGeneratesAfterInput input output K := by
  exact novel_of_finite_range_difference hPresentation.2.2 hNovelRange

end Stage3Case019Partial

-- The exact endpoint remains open in this partial formalization.
-- theorem stage3_result : Stage3Case019.MainClaim := by
--   exact ⟨stage3_countable_half_density, stage3_uncountable_separation⟩
