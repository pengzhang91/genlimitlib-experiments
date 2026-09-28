import Stage3Model
import GenLimit.Paper39_DenseGeneration.Patient.Main

namespace Stage3Case025

private theorem finset_seen_by
    (input : Stream) (F : Finset ℕ)
    (hF : (F : Set ℕ) ⊆ Set.range input) :
    ∃ T, ∀ x ∈ F, ∃ s, s < T ∧ input s = x := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert x F hx ih =>
      have hxrange : x ∈ Set.range input := hF (by simp)
      obtain ⟨sx, hsx⟩ := hxrange
      have hsub : (F : Set ℕ) ⊆ Set.range input := by
        intro y hy
        exact hF (by simp [hy])
      obtain ⟨T, hT⟩ := ih hsub
      refine ⟨max T (sx + 1), ?_⟩
      intro y hy
      simp only [Finset.mem_insert] at hy
      rcases hy with rfl | hy
      · exact ⟨sx, lt_of_lt_of_le (Nat.lt_succ_self sx) (Nat.le_max_right _ _), hsx⟩
      · obtain ⟨s, hs, heq⟩ := hT y hy
        exact ⟨s, lt_of_lt_of_le hs (Nat.le_max_left _ _), heq⟩

private theorem novelty_of_finite_extension
    {input output : Stream} {K : Language} (F : Finset ℕ)
    (hP : GenLimit.Presents input (K ∪ (F : Set ℕ)))
    (hNovel : GenLimit.NovelGeneratesInLimit input output
      (K ∪ (F : Set ℕ))) :
    GenLimit.NovelGeneratesInLimit input output K := by
  have hcoverage : (F : Set ℕ) ⊆ Set.range input := by
    intro x hx
    rw [hP]
    exact Set.mem_union_right K hx
  obtain ⟨S, hS⟩ := finset_seen_by input F hcoverage
  obtain ⟨T, hT⟩ := hNovel
  refine ⟨max T S, ?_⟩
  intro t ht
  have htT : T ≤ t := le_trans (Nat.le_max_left _ _) ht
  have htS : S ≤ t := le_trans (Nat.le_max_right _ _) ht
  obtain ⟨hmem, hfresh, hrepeat⟩ := hT t htT
  refine ⟨?_, hfresh, hrepeat⟩
  rcases hmem with hK | hFmem
  · exact hK
  · obtain ⟨s, hsS, hinput⟩ := hS (output t) hFmem
    exact False.elim (hfresh (GenLimit.mem_sample_iff.mpr
      ⟨s, lt_of_lt_of_le hsS (Nat.le_succ_of_le htS), hinput⟩))

end Stage3Case025
