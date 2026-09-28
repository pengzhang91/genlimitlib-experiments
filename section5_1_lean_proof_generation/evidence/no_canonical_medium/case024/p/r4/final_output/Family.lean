import «output».Generator

open Filter
open scoped Topology

namespace Case024

noncomputable def marker (k : ℕ) : ℕ := (k + 1)^2 + 1

lemma marker_injective : Function.Injective marker := by
  intro a b h
  unfold marker at h
  have hs : (a + 1)^2 = (b + 1)^2 := by omega
  have hab : a + 1 = b + 1 := (Nat.pow_left_injective (by decide : 2 ≠ 0)) hs
  omega

lemma marker_not_square (k : ℕ) : marker k ∉ squares := by
  intro hsq
  rcases hsq with ⟨m, hm⟩
  change m^2 = marker k at hm
  have hlo : (k + 1)^2 < m^2 := by rw [hm]; unfold marker; omega
  have hhi : m^2 < (k + 2)^2 := by rw [hm]; unfold marker; nlinarith [Nat.zero_le k]
  have hml : k + 1 < m := (Nat.pow_left_strictMono (by decide : 2 ≠ 0)).lt_iff_lt.mp hlo
  have hmu : m < k + 2 := (Nat.pow_left_strictMono (by decide : 2 ≠ 0)).lt_iff_lt.mp hhi
  omega

noncomputable def finiteExtension (i : ℕ) : Set ℕ :=
  squares ∪ {x | ∃ k < i, x = marker k}

lemma squares_subset_finiteExtension (i : ℕ) : squares ⊆ finiteExtension i :=
  Set.subset_union_left

lemma marker_mem_finiteExtension {k i : ℕ} (hki : k < i) : marker k ∈ finiteExtension i := by
  exact Or.inr ⟨k, hki, rfl⟩

lemma marker_not_mem_finiteExtension (i : ℕ) : marker i ∉ finiteExtension i := by
  intro h
  rcases h with hs | ⟨k, hki, hk⟩
  · exact marker_not_square i hs
  · exact (Nat.ne_of_lt hki) (marker_injective hk).symm

lemma noiseCount_mono {K L : Set ℕ} (hKL : K ⊆ L) (n : ℕ) :
    GenLimit.InfiniteContamination.noiseCount commonStream L n ≤
      GenLimit.InfiniteContamination.noiseCount commonStream K n := by
  classical
  unfold GenLimit.InfiniteContamination.noiseCount
  apply Finset.card_le_card
  intro t ht
  simp only [Finset.mem_filter, Finset.mem_range] at ht ⊢
  exact ⟨ht.1, fun htK => ht.2 (hKL htK)⟩

lemma commonStream_legal_superset {K : Set ℕ} (hsub : squares ⊆ K) :
    Stage3Case024.Legal commonStream K := by
  refine ⟨squares_infinite.mono hsub, commonStream_injective, ?_, ?_⟩
  · intro x hx
    exact commonStream_surjective x
  · unfold GenLimit.InfiniteContamination.VanishingNoise
    apply squeeze_zero
      (f := GenLimit.InfiniteContamination.empiricalNoiseRate commonStream K)
      (g := GenLimit.InfiniteContamination.empiricalNoiseRate commonStream squares)
    · intro n
      unfold GenLimit.InfiniteContamination.empiricalNoiseRate
      positivity
    · intro n
      unfold GenLimit.InfiniteContamination.empiricalNoiseRate
      by_cases hn : n = 0
      · simp [hn, GenLimit.InfiniteContamination.empiricalNoiseRate]
      · simp only [hn, if_false]
        have hcast : (GenLimit.InfiniteContamination.noiseCount commonStream K n : ℝ) ≤
            (GenLimit.InfiniteContamination.noiseCount commonStream squares n : ℝ) := by
          exact_mod_cast noiseCount_mono hsub n
        exact div_le_div_of_nonneg_right hcast (Nat.cast_nonneg _)
    · exact commonStream_vanishingNoise_squares

noncomputable def nestedFamily (r : ℕ) (i : Fin r) : Set ℕ :=
  if (i : ℕ) + 1 = r then Set.univ else finiteExtension i

lemma nestedFamily_legal {r : ℕ} (i : Fin r) :
    Stage3Case024.Legal commonStream (nestedFamily r i) := by
  unfold nestedFamily
  split
  · exact commonStream_legal_univ
  · exact commonStream_legal_superset (squares_subset_finiteExtension i)

lemma nestedFamily_strict {r : ℕ} (hr : 2 ≤ r) :
    Stage3Case024.StrictlyNested (nestedFamily r) := by
  intro i j hij
  have hij' : (i : ℕ) < (j : ℕ) := hij
  have hi_not_last : (i : ℕ) + 1 ≠ r := by omega
  by_cases hj_last : (j : ℕ) + 1 = r
  · change (if (i : ℕ) + 1 = r then Set.univ else finiteExtension i) ⊂
      (if (j : ℕ) + 1 = r then Set.univ else finiteExtension j)
    simp only [hj_last, hi_not_last, if_pos, if_neg]
    refine ⟨Set.subset_univ _, ?_⟩
    intro hrev
    exact marker_not_mem_finiteExtension i (hrev (Set.mem_univ (marker i)))
  · change (if (i : ℕ) + 1 = r then Set.univ else finiteExtension i) ⊂
      (if (j : ℕ) + 1 = r then Set.univ else finiteExtension j)
    simp only [hj_last, hi_not_last, if_pos, if_neg]
    refine ⟨?_, ?_⟩
    · intro x hx
      rcases hx with hx | ⟨k, hki, hk⟩
      · exact Or.inl hx
      · exact Or.inr ⟨k, hki.trans hij', hk⟩
    · intro hrev
      exact marker_not_mem_finiteExtension i
        (hrev (marker_mem_finiteExtension hij'))

end Case024
