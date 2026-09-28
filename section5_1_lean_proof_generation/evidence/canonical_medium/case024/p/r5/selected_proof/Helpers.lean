import Stage3Model
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

open Filter MeasureTheory
open scoped Topology

namespace Case024

noncomputable section

open Classical

def sq (n : ℕ) : ℕ := n * n

def Squares : Set ℕ := Set.range sq

lemma sq_injective : Function.Injective sq := by
  intro a b h
  dsimp [sq] at h
  nlinarith

lemma squares_infinite : Squares.Infinite :=
  Set.infinite_range_of_injective sq_injective

def gap (n : ℕ) : ℕ := (n + 1) * (n + 1) + (n + 1)

lemma gap_not_square (n : ℕ) : gap n ∉ Squares := by
  rintro ⟨k, hk⟩
  dsimp [gap, sq] at hk
  by_cases h : k ≤ n + 1
  · have : k * k ≤ (n + 1) * (n + 1) := Nat.mul_self_le_mul_self h
    omega
  · have : n + 2 ≤ k := by omega
    have hsq : (n + 2) * (n + 2) ≤ k * k := Nat.mul_self_le_mul_self this
    nlinarith

lemma gap_injective : Function.Injective gap := by
  intro a b h
  dsimp [gap] at h
  nlinarith

lemma nonsquares_infinite : Squaresᶜ.Infinite := by
  exact Set.Infinite.mono (show Set.range gap ⊆ Squaresᶜ by
    rintro _ ⟨n, rfl⟩
    exact gap_not_square n) (Set.infinite_range_of_injective gap_injective)

noncomputable def input (t : ℕ) : ℕ :=
  if t ∈ Squares then
    Nat.nth (fun n => n ∉ Squares) (Nat.count (fun n => n ∈ Squares) t)
  else
    Nat.nth (fun n => n ∈ Squares) (Nat.count (fun n => n ∉ Squares) t)

lemma count_rank_injective {p : ℕ → Prop} [DecidablePred p] {a b : ℕ}
    (ha : p a) (hb : p b) (h : Nat.count p a = Nat.count p b) : a = b := by
  rcases lt_trichotomy a b with hab | hab | hab
  · have := Nat.count_strict_mono ha hab
    omega
  · exact hab
  · have := Nat.count_strict_mono hb hab
    omega

lemma input_injective : Function.Injective input := by
  intro a b hab
  by_cases ha : a ∈ Squares <;> by_cases hb : b ∈ Squares
  · simp [input, ha, hb] at hab
    apply count_rank_injective ha hb
    exact (Nat.nth_injective (by simpa only [Set.mem_compl_iff] using nonsquares_infinite)) hab
  · simp [input, ha, hb] at hab
    have hleft : Nat.nth (fun n => n ∉ Squares) (Nat.count (fun n => n ∈ Squares) a) ∉ Squares :=
      Nat.nth_mem_of_infinite (by simpa only [Set.mem_compl_iff] using nonsquares_infinite) _
    have hright : Nat.nth (fun n => n ∈ Squares) (Nat.count (fun n => n ∉ Squares) b) ∈ Squares :=
      Nat.nth_mem_of_infinite (by simpa using squares_infinite) _
    rw [hab] at hleft
    exact (hleft hright).elim
  · simp [input, ha, hb] at hab
    have hleft : Nat.nth (fun n => n ∈ Squares) (Nat.count (fun n => n ∉ Squares) a) ∈ Squares :=
      Nat.nth_mem_of_infinite (by simpa using squares_infinite) _
    have hright : Nat.nth (fun n => n ∉ Squares) (Nat.count (fun n => n ∈ Squares) b) ∉ Squares :=
      Nat.nth_mem_of_infinite (by simpa only [Set.mem_compl_iff] using nonsquares_infinite) _
    rw [hab] at hleft
    exact (hright hleft).elim
  · simp [input, ha, hb] at hab
    apply count_rank_injective (p := fun n => n ∉ Squares) ha hb
    exact (Nat.nth_injective (by simpa using squares_infinite)) hab

lemma count_at_nth_pred {p : ℕ → Prop} [DecidablePred p]
    (hp : {n | p n}.Infinite) (k : ℕ) :
    Nat.count p (Nat.nth p k) = k :=
  Nat.count_nth_of_infinite hp k

lemma input_surjective : Function.Surjective input := by
  intro x
  by_cases hx : x ∈ Squares
  · have hs : {n | n ∈ Squares}.Infinite := by simpa using squares_infinite
    have hx' : x ∈ Set.range (Nat.nth fun n => n ∈ Squares) := by
      rw [Nat.range_nth_of_infinite hs]
      exact hx
    obtain ⟨k, rfl⟩ := hx'
    let t := Nat.nth (fun n => n ∉ Squares) k
    refine ⟨t, ?_⟩
    have hc : {n | n ∉ Squares}.Infinite := by simpa only [Set.mem_compl_iff] using nonsquares_infinite
    have ht : t ∉ Squares := Nat.nth_mem_of_infinite hc k
    simp [input, t, ht, Nat.count_nth_of_infinite hc]
  · have hc : {n | n ∉ Squares}.Infinite := by simpa only [Set.mem_compl_iff] using nonsquares_infinite
    have hx' : x ∈ Set.range (Nat.nth fun n => n ∉ Squares) := by
      rw [Nat.range_nth_of_infinite hc]
      exact hx
    obtain ⟨k, rfl⟩ := hx'
    let t := Nat.nth (fun n => n ∈ Squares) k
    refine ⟨t, ?_⟩
    have hs : {n | n ∈ Squares}.Infinite := by simpa using squares_infinite
    have ht : t ∈ Squares := Nat.nth_mem_of_infinite hs k
    simp [input, t, ht, Nat.count_nth_of_infinite hs]

lemma input_range : Set.range input = Set.univ := Set.range_eq_univ.mpr input_surjective

lemma input_mem_squares_iff (t : ℕ) : input t ∈ Squares ↔ t ∉ Squares := by
  by_cases ht : t ∈ Squares
  · have hc : {n | n ∉ Squares}.Infinite := by simpa only [Set.mem_compl_iff] using nonsquares_infinite
    simp [input, ht, Nat.nth_mem_of_infinite hc]
  · have hs : {n | n ∈ Squares}.Infinite := by simpa using squares_infinite
    simp [input, ht, Nat.nth_mem_of_infinite hs]

lemma noiseCount_squares (n : ℕ) :
    GenLimit.InfiniteContamination.noiseCount input Squares n =
      Nat.count (fun t => t ∈ Squares) n := by
  classical
  simp only [GenLimit.InfiniteContamination.noiseCount, Nat.count_eq_card_filter_range]
  congr 1
  ext t
  simp [input_mem_squares_iff]

lemma square_root_bound {x n : ℕ} (hx : x ∈ Squares) (hxn : x < n) :
    ∃ k < n.sqrt + 1, sq k = x := by
  obtain ⟨k, rfl⟩ := hx
  refine ⟨k, ?_, rfl⟩
  have hk : k ≤ n.sqrt := (Nat.le_sqrt).2 (by dsimp [sq] at hxn ⊢; omega)
  omega

lemma count_squares_le (n : ℕ) :
    Nat.count (fun x => x ∈ Squares) n ≤ n.sqrt + 1 := by
  classical
  rw [Nat.count_eq_card_filter_range]
  let f : Finset ℕ := (Finset.range (n.sqrt + 1)).image sq
  calc
    ((Finset.range n).filter fun x => x ∈ Squares).card ≤ f.card := by
      apply Finset.card_le_card
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_range] at hx
      simp only [f, Finset.mem_image]
      obtain ⟨k, hk, rfl⟩ := square_root_bound hx.2 hx.1
      exact ⟨k, by simpa, rfl⟩
    _ ≤ (Finset.range (n.sqrt + 1)).card := Finset.card_image_le
    _ = n.sqrt + 1 := Finset.card_range _

lemma tendsto_sqrt_cast_atTop :
    Tendsto (fun n : ℕ => (n.sqrt : ℝ)) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro b
  obtain ⟨m : ℕ, hm : b ≤ m⟩ := exists_nat_ge b
  refine ⟨m * m, ?_⟩
  intro n hn
  exact hm.trans (by exact_mod_cast ((Nat.le_sqrt).2 hn))

lemma tendsto_sqrt_add_one_div :
    Tendsto (fun n : ℕ => ((n.sqrt + 1 : ℕ) : ℝ) / n) atTop (nhds 0) := by
  have hsqrt_inv : Tendsto (fun n : ℕ => ((n.sqrt : ℝ))⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_sqrt_cast_atTop
  have hone_div : Tendsto (fun n : ℕ => (1 : ℝ) / n) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  apply squeeze_zero' (Filter.Eventually.of_forall fun n => by positivity) _ (by simpa using hsqrt_inv.add hone_div)
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [Nat.cast_add, Nat.cast_one, add_div]
  apply add_le_add
  · have hspos : (0 : ℝ) < n.sqrt := by
      exact_mod_cast (Nat.sqrt_pos.2 hn)
    calc
      (n.sqrt : ℝ) / n ≤ (n.sqrt : ℝ) / ((n.sqrt : ℝ) * n.sqrt) := by
        gcongr
        exact_mod_cast Nat.sqrt_le n
      _ = ((n.sqrt : ℝ))⁻¹ := by field_simp
  · simp [one_div]

lemma tendsto_count_squares_div :
    Tendsto (fun n : ℕ => (Nat.count (fun x => x ∈ Squares) n : ℝ) / n)
      atTop (nhds 0) := by
  apply squeeze_zero' (Filter.Eventually.of_forall fun n => by positivity) _ tendsto_sqrt_add_one_div
  filter_upwards with n
  gcongr
  exact count_squares_le n

lemma vanishingNoise_squares :
    GenLimit.InfiniteContamination.VanishingNoise input Squares := by
  unfold GenLimit.InfiniteContamination.VanishingNoise
  have h := tendsto_count_squares_div
  apply h.congr'
  filter_upwards [eventually_ne_atTop 0] with n hn
  simp [GenLimit.InfiniteContamination.empiricalNoiseRate, hn, noiseCount_squares]

lemma legal_squares : Stage3Case024.Legal input Squares := by
  refine ⟨squares_infinite, input_injective, ?_, vanishingNoise_squares⟩
  intro x hx
  rw [input_range]
  trivial

lemma legal_univ : Stage3Case024.Legal input Set.univ := by
  refine ⟨Set.infinite_univ, input_injective, ?_, ?_⟩
  · unfold GenLimit.InfiniteContamination.NoOmissions
    rw [input_range]
  · unfold GenLimit.InfiniteContamination.VanishingNoise
    have hz : GenLimit.InfiniteContamination.empiricalNoiseRate input Set.univ =
        (fun _ : ℕ => (0 : ℝ)) := by
      funext n
      simp [GenLimit.InfiniteContamination.empiricalNoiseRate,
        GenLimit.InfiniteContamination.noiseCount]
    rw [hz]
    exact tendsto_const_nhds

end

end Case024
