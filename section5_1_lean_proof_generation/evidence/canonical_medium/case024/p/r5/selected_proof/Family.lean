import Obstruction

open Filter MeasureTheory
open scoped Topology

namespace Case024
noncomputable section
open Classical

lemma noiseCount_mono {K L : Set ℕ} (h : K ⊆ L) (n : ℕ) :
    GenLimit.InfiniteContamination.noiseCount input L n ≤
      GenLimit.InfiniteContamination.noiseCount input K n := by
  unfold GenLimit.InfiniteContamination.noiseCount
  apply Finset.card_le_card
  intro t ht
  simp only [Finset.mem_filter, Finset.mem_range] at ht ⊢
  exact ⟨ht.1, fun hK => ht.2 (h hK)⟩

lemma legal_of_squares_subset {K : Set ℕ} (hK : Squares ⊆ K) (hinf : K.Infinite) :
    Stage3Case024.Legal input K := by
  refine ⟨hinf, input_injective, ?_, ?_⟩
  · unfold GenLimit.InfiniteContamination.NoOmissions
    rw [input_range]
    exact Set.subset_univ _
  · unfold GenLimit.InfiniteContamination.VanishingNoise
    apply squeeze_zero' (Filter.Eventually.of_forall fun n => by
      unfold GenLimit.InfiniteContamination.empiricalNoiseRate
      positivity) _ vanishingNoise_squares
    filter_upwards with n
    unfold GenLimit.InfiniteContamination.empiricalNoiseRate
    by_cases hn : n = 0
    · simp [hn]
    · simp only [hn, if_false]
      gcongr
      exact noiseCount_mono hK n

def additions (j : ℕ) : Set ℕ := Set.range gap ∩ {x | ∃ k < j, gap k = x}

def family {r : ℕ} (j : Fin r) : Set ℕ :=
  if (j : ℕ) + 1 = r then Set.univ else Squares ∪ additions j

lemma additions_mono {i j : ℕ} (h : i ≤ j) : additions i ⊆ additions j := by
  rintro x ⟨hr, k, hk, heq⟩
  exact ⟨hr, k, hk.trans_le h, heq⟩

lemma gap_mem_additions {i j : ℕ} (h : i < j) : gap i ∈ additions j := by
  exact ⟨⟨i, rfl⟩, i, h, rfl⟩

lemma gap_not_mem_additions (i : ℕ) : gap i ∉ additions i := by
  rintro ⟨_, k, hk, heq⟩
  have := gap_injective heq
  omega

lemma family_infinite {r : ℕ} (j : Fin r) : (family j).Infinite := by
  by_cases hlast : (j : ℕ) + 1 = r
  · simpa [family, hlast] using (Set.infinite_univ : (Set.univ : Set ℕ).Infinite)
  · apply Set.Infinite.mono (show Squares ⊆ family j by simp [family, hlast]) squares_infinite

lemma family_legal {r : ℕ} (j : Fin r) : Stage3Case024.Legal input (family j) := by
  apply legal_of_squares_subset
  · by_cases hlast : (j : ℕ) + 1 = r <;> simp [family, hlast]
  · exact family_infinite j

lemma family_strictlyNested {r : ℕ} (hr : 2 ≤ r) : Stage3Case024.StrictlyNested (@family r) := by
  intro i j hij
  have hjle : (j : ℕ) + 1 ≤ r := j.isLt
  by_cases hjlast : (j : ℕ) + 1 = r
  · have hilast : (i : ℕ) + 1 ≠ r := by omega
    change family i ⊂ family j
    simp only [family, hjlast, hilast, if_pos, if_neg]
    refine ⟨Set.subset_univ _, fun hreverse => ?_⟩
    let w := gap r
    have hw := hreverse (Set.mem_univ w)
    rcases hw with hw | hw
    · exact gap_not_square r hw
    · rcases hw with ⟨_, k, hk, heq⟩
      have := gap_injective heq
      omega
  · have hilast : (i : ℕ) + 1 ≠ r := by omega
    change family i ⊂ family j
    simp only [family, hjlast, hilast, if_pos, if_neg]
    refine ⟨?_, fun hreverse => ?_⟩
    · intro x hx
      rcases hx with hx | hx
      · exact Or.inl hx
      · exact Or.inr (additions_mono (Nat.le_of_lt hij) hx)
    have hw := hreverse (Or.inr (gap_mem_additions hij))
    rcases hw with hw | hw
    · exact gap_not_square i hw
    · exact gap_not_mem_additions i hw

noncomputable def safeGen : Stage3Case024.OnlineGenerator :=
  fun t inp _ => sq ((t + 1) * (1 + ∑ i, inp i))

noncomputable def safeOutput (stream : Stage3Case024.Stream) : Stage3Case024.Stream :=
  fun t => sq ((t + 1) * (1 + ∑ i : Fin (t + 1), stream i))

lemma safe_follows (stream : Stage3Case024.Stream) :
    Stage3Case024.Follows safeGen stream (safeOutput stream) := by
  intro t
  rfl

lemma fin_le_sum {n : ℕ} (f : Fin n → ℕ) (i : Fin n) : f i ≤ ∑ j, f j := by
  exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)

lemma safeOutput_gt_input (stream : Stage3Case024.Stream) (t s : ℕ) (hs : s ≤ t) :
    stream s < safeOutput stream t := by
  have hsum : stream s ≤ ∑ i : Fin (t + 1), stream i :=
    fin_le_sum (fun i : Fin (t + 1) => stream i) ⟨s, by omega⟩
  unfold safeOutput sq
  let b := (t + 1) * (1 + ∑ i : Fin (t + 1), stream i)
  change stream s < b * b
  have hb : stream s < b := by
    dsimp [b]
    nlinarith
  exact hb.trans_le (Nat.le_mul_self b)

lemma sum_prefix_mono (stream : ℕ → ℕ) {a b : ℕ} (h : a ≤ b) :
    (∑ i : Fin a, stream i) ≤ ∑ i : Fin b, stream i := by
  classical
  rw [Fin.sum_univ_eq_sum_range stream a, Fin.sum_univ_eq_sum_range stream b]
  exact Finset.sum_le_sum_of_subset_of_nonneg (s := Finset.range a) (t := Finset.range b)
    (fun i hi => Finset.mem_range.2 ((Finset.mem_range.1 hi).trans_le h))
    (fun i _ _ => Nat.zero_le (stream i))

lemma safeOutput_strictMono (stream : Stage3Case024.Stream) : StrictMono (safeOutput stream) := by
  intro a b hab
  unfold safeOutput sq
  have hsum : (∑ i : Fin (a + 1), stream i) ≤ ∑ i : Fin (b + 1), stream i :=
    sum_prefix_mono stream (by omega)
  have hbase : (a + 1) * (1 + ∑ i : Fin (a + 1), stream i) <
      (b + 1) * (1 + ∑ i : Fin (b + 1), stream i) := by
    calc
      (a + 1) * (1 + ∑ i : Fin (a + 1), stream i) <
          (b + 1) * (1 + ∑ i : Fin (a + 1), stream i) :=
        Nat.mul_lt_mul_of_pos_right (by omega) (by positivity)
      _ ≤ (b + 1) * (1 + ∑ i : Fin (b + 1), stream i) := by
        exact Nat.mul_le_mul_left _ (Nat.add_le_add_left hsum 1)
  exact Nat.mul_self_lt_mul_self hbase

lemma safe_novel (stream : Stage3Case024.Stream) :
    GenLimit.NovelGeneratesInLimit stream (safeOutput stream) Squares := by
  refine ⟨0, fun t _ => ?_⟩
  refine ⟨⟨(t + 1) * (1 + ∑ i : Fin (t + 1), stream i), rfl⟩, ?_, ?_⟩
  · intro hmem
    simp only [GenLimit.sample, Finset.mem_image, Finset.mem_range] at hmem
    obtain ⟨s, hs, heq⟩ := hmem
    exact (safeOutput_gt_input stream t s (by omega)).ne (by simpa [safeOutput] using heq)
  · intro s hs
    exact (safeOutput_strictMono stream hs).ne

lemma family_globallyFeasible {r : ℕ} : Stage3Case024.GloballyFeasible (@family r) := by
  refine ⟨safeGen, fun stream _ => ⟨safeOutput stream, safe_follows stream, ?_⟩⟩
  intro j
  unfold Stage3Case024.EventuallyFreshValidPath
  obtain ⟨T, hT⟩ := safe_novel stream
  refine ⟨T, fun t ht => ?_⟩
  have hsquares := (hT t ht).1
  refine ⟨?_, (hT t ht).2⟩
  by_cases hlast : (j : ℕ) + 1 = r
  · simp [family, hlast]
  · rw [family, if_neg hlast]
    exact Or.inl hsquares

lemma family_manyObstruction {r : ℕ} (hr : 2 ≤ r) :
    Stage3Case024.ManyTargetObstruction (@family r) input := by
  intro Ω _ μ _ gen output _ _ _ hvalid
  let j : Fin r := ⟨r - 1, by omega⟩
  refine ⟨j, ?_⟩
  have hj : (j : ℕ) + 1 = r := by simp [j]; omega
  rw [show family j = Set.univ by simp [family, hj]]
  exact expected_univ_zero μ input output (hvalid ⟨0, by omega⟩ |>.mono fun ω hω => by
    obtain ⟨T, hT⟩ := hω
    refine ⟨T, fun t ht => ?_⟩
    have hsq : family (⟨0, by omega⟩ : Fin r) = Squares ∪ additions 0 := by
      simp [family]
      omega
    rw [hsq] at hT
    have := hT t ht
    refine ⟨?_, this.2⟩
    rcases this.1 with hs | ha
    · exact hs
    · rcases ha with ⟨_, k, hk, _⟩
      omega)

lemma manyTargetWitness {r : ℕ} (hr : 2 ≤ r) :
    Stage3Case024.ManyTargetWitness (@family r) input := by
  exact ⟨family_strictlyNested hr, family_legal, family_globallyFeasible,
    family_manyObstruction hr⟩

end
end Case024
