import «output».Sparse
import Mathlib.Data.Nat.Nth

open Filter
open scoped Topology

namespace Case024

noncomputable def swapStream (p : ℕ → Prop) : ℕ → ℕ := by
  classical
  exact fun t => if p t then Nat.nth (fun x => ¬ p x) (Nat.count p t)
  else Nat.nth p (Nat.count (fun x => ¬ p x) t)

lemma swapStream_injective (p : ℕ → Prop)
    (hp : (setOf p).Infinite) (hnp : (setOf fun x => ¬ p x).Infinite) :
    Function.Injective (swapStream p) := by
  classical
  intro a b hab
  by_cases ha : p a <;> by_cases hb : p b
  · simp only [swapStream, if_pos ha, if_pos hb] at hab
    exact Nat.count_injective ha hb ((Nat.nth_injective hnp) hab)
  · have hma := Nat.nth_mem_of_infinite hnp (Nat.count p a)
    have hmb := Nat.nth_mem_of_infinite hp (Nat.count (fun x => ¬p x) b)
    simp only [swapStream, if_pos ha, if_neg hb] at hab
    rw [hab] at hma
    exact False.elim (hma hmb)
  · have hma := Nat.nth_mem_of_infinite hp (Nat.count (fun x => ¬p x) a)
    have hmb := Nat.nth_mem_of_infinite hnp (Nat.count p b)
    simp only [swapStream, if_neg ha, if_pos hb] at hab
    rw [hab] at hma
    exact False.elim (hmb hma)
  · simp only [swapStream, if_neg ha, if_neg hb] at hab
    exact Nat.count_injective ha hb ((Nat.nth_injective hp) hab)

lemma swapStream_surjective (p : ℕ → Prop)
    (hp : (setOf p).Infinite) (hnp : (setOf fun x => ¬ p x).Infinite) :
    Function.Surjective (swapStream p) := by
  classical
  intro x
  by_cases hx : p x
  · let t := Nat.nth (fun y => ¬p y) (Nat.count p x)
    refine ⟨t, ?_⟩
    have ht : ¬p t := Nat.nth_mem_of_infinite hnp _
    simp only [swapStream, if_neg ht]
    rw [Nat.count_nth_of_infinite hnp, Nat.nth_count hx]
  · let t := Nat.nth p (Nat.count (fun y => ¬p y) x)
    refine ⟨t, ?_⟩
    have ht : p t := Nat.nth_mem_of_infinite hp _
    simp only [swapStream, if_pos ht]
    rw [Nat.count_nth_of_infinite hp, Nat.nth_count hx]

lemma swapStream_mem_iff (p : ℕ → Prop)
    (hp : (setOf p).Infinite) (hnp : (setOf fun x => ¬ p x).Infinite) (t : ℕ) :
    p (swapStream p t) ↔ ¬ p t := by
  classical
  by_cases ht : p t
  · rw [swapStream, if_pos ht]
    constructor
    · intro hout hpt
      exact (Nat.nth_mem_of_infinite hnp _) hout
    · intro hnot
      exact False.elim (hnot ht)
  · rw [swapStream, if_neg ht]
    constructor
    · intro _
      exact ht
    · intro _
      exact Nat.nth_mem_of_infinite hp _

lemma squares_infinite : squares.Infinite := by
  exact (Set.infinite_range_of_injective (Nat.pow_left_injective (by decide : 2 ≠ 0)))

lemma nonsquares_infinite : (squaresᶜ).Infinite := by
  intro hfin
  obtain ⟨M, hM⟩ := hfin.exists_le
  let x := (M + 1)^2 + 1
  have hxgt : M < x := by
    dsimp [x]
    nlinarith [Nat.zero_le M]
  have hxns : x ∈ squaresᶜ := by
    intro hsq
    rcases hsq with ⟨k, hk⟩
    change k^2 = x at hk
    have hlo : (M + 1)^2 < k^2 := by
      rw [hk]
      dsimp [x]
      omega
    have hhi : k^2 < (M + 2)^2 := by
      rw [hk]
      dsimp [x]
      nlinarith [Nat.zero_le M]
    have hkl : M + 1 < k := (Nat.pow_left_strictMono (by decide : 2 ≠ 0)).lt_iff_lt.mp hlo
    have hku : k < M + 2 := (Nat.pow_left_strictMono (by decide : 2 ≠ 0)).lt_iff_lt.mp hhi
    omega
  exact (not_le_of_gt hxgt) (hM x hxns)

noncomputable abbrev commonStream : ℕ → ℕ :=
  swapStream (fun x => x ∈ squares)

lemma commonStream_injective : Function.Injective commonStream := by
  exact swapStream_injective _ squares_infinite nonsquares_infinite

lemma commonStream_surjective : Function.Surjective commonStream := by
  exact swapStream_surjective _ squares_infinite nonsquares_infinite

end Case024

namespace Case024

lemma commonStream_mem_squares_iff (t : ℕ) : commonStream t ∈ squares ↔ t ∉ squares := by
  exact swapStream_mem_iff _ squares_infinite nonsquares_infinite t

lemma noiseCount_common_squares (n : ℕ) :
    GenLimit.InfiniteContamination.noiseCount commonStream squares n =
      GenLimit.PatientScope.prefixCount squares n := by
  classical
  unfold GenLimit.InfiniteContamination.noiseCount
    GenLimit.PatientScope.prefixCount GenLimit.PatientScope.prefixFinset
  congr 1
  ext t
  simp only [Finset.mem_filter, Finset.mem_range]
  rw [commonStream_mem_squares_iff]
  tauto

lemma commonStream_vanishingNoise_squares :
    GenLimit.InfiniteContamination.VanishingNoise commonStream squares := by
  unfold GenLimit.InfiniteContamination.VanishingNoise
    GenLimit.InfiniteContamination.empiricalNoiseRate
  have hratio := tendsto_square_prefix_ratio_zero
  apply hratio.congr'
  filter_upwards [eventually_ne_atTop 0] with n hn
  simp only [hn, if_false, noiseCount_common_squares]

lemma commonStream_legal_squares : Stage3Case024.Legal commonStream squares := by
  refine ⟨squares_infinite, commonStream_injective, ?_, commonStream_vanishingNoise_squares⟩
  intro x hx
  exact commonStream_surjective x

lemma commonStream_legal_univ : Stage3Case024.Legal commonStream Set.univ := by
  refine ⟨Set.infinite_univ, commonStream_injective, ?_, ?_⟩
  · intro x _
    exact commonStream_surjective x
  · unfold GenLimit.InfiniteContamination.VanishingNoise
      GenLimit.InfiniteContamination.empiricalNoiseRate
    have : (fun _ : ℕ => (0 : ℝ)) =ᶠ[atTop]
        (fun n => if n = 0 then 0 else
          (GenLimit.InfiniteContamination.noiseCount commonStream Set.univ n : ℝ) / n) := by
      filter_upwards with n
      simp [GenLimit.InfiniteContamination.noiseCount]
    exact tendsto_const_nhds.congr' this

end Case024
