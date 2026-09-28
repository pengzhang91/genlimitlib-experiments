import Stage3Model

#check Set.Infinite.exists_not_mem_finset
#check Nat.find
#check Nat.find_spec
#check Nat.find_min'
#check Finset.card_le_card
#check Finset.card_image_iff
#check Finset.card_image_le
#check Finset.filter_subset
#check Filter.liminf_le_liminf
#check Filter.liminf_le_liminf_of_le
#check Filter.liminf_mono
#check Filter.EventuallyLE
#check tendsto_natCast_atTop_atTop
#check tendsto_inv_atTop_zero
#check Filter.Tendsto.liminf_le_liminf
#check Filter.liminf_const
#check Set.ncard_le_ncard
#check Set.ncard_diff_le
#check Set.Finite.toFinset
#check Finset.exists_max_image
#check Finset.sup'_le_iff

open Stage3Case017

noncomputable def testPick (S : Set ℕ) (blocked : Finset ℕ) : ℕ := by
  classical
  by_cases h : S.Infinite
  · exact Nat.find (h.exists_not_mem_finset blocked)
  · exact Nat.find (Set.infinite_univ.exists_not_mem_finset blocked)

theorem testPick_not_mem (S : Set ℕ) (blocked : Finset ℕ) :
    testPick S blocked ∉ blocked := by
  classical
  unfold testPick
  split <;> rename_i h
  · exact (Nat.find_spec (h.exists_not_mem_finset blocked)).2
  · exact (Nat.find_spec (Set.infinite_univ.exists_not_mem_finset blocked)).2

noncomputable def traj (gen : OnlineGenerator) (input : Stream) (t : ℕ) : ℕ :=
