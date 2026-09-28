import Stage3Model
import Mathlib

open Filter MeasureTheory
open scoped Topology

namespace Case024Formalization

abbrev Language := Stage3Case024.Language
abbrev Stream := Stage3Case024.Stream

def squareTime (t : ℕ) : Prop := ∃ k, t = k * k

noncomputable instance (t : ℕ) : Decidable (squareTime t) := Classical.dec _

noncomputable def squareStream (t : ℕ) : ℕ :=
  if squareTime t then 2 * Nat.sqrt t + 1 else 2 * t

def squareCore : Language :=
  {x | ∃ t, ¬ squareTime t ∧ x = 2 * t}

def squareRange : Language := Set.range squareStream

lemma squareTime_sq (k : ℕ) : squareTime (k * k) := ⟨k, rfl⟩

lemma sqrt_sq (k : ℕ) : Nat.sqrt (k * k) = k := by simp

lemma squareStream_sq (k : ℕ) : squareStream (k * k) = 2 * k + 1 := by
  simp [squareStream, squareTime_sq]

lemma squareStream_of_not_square {t : ℕ} (ht : ¬ squareTime t) :
    squareStream t = 2 * t := by simp [squareStream, ht]

lemma squareStream_injective : Function.Injective squareStream := by
  intro a b hab
  by_cases ha : squareTime a
  · by_cases hb : squareTime b
    · rcases ha with ⟨ka, rfl⟩
      rcases hb with ⟨kb, rfl⟩
      simp only [squareStream_sq] at hab
      have hkab : ka = kb := by omega
      subst kb
      rfl
    · rw [squareStream, if_pos ha, squareStream, if_neg hb] at hab
      omega
  · by_cases hb : squareTime b
    · rw [squareStream, if_neg ha, squareStream, if_pos hb] at hab
      omega
    · rw [squareStream, if_neg ha, squareStream, if_neg hb] at hab
      omega

lemma squareCore_subset_range : squareCore ⊆ squareRange := by
  rintro x ⟨t, ht, rfl⟩
  exact ⟨t, squareStream_of_not_square ht⟩

lemma odd_mem_squareRange (k : ℕ) : 2 * k + 1 ∈ squareRange := by
  exact ⟨k * k, squareStream_sq k⟩

lemma squareCore_even {x : ℕ} (hx : x ∈ squareCore) : Even x := by
  rcases hx with ⟨t, _, rfl⟩
  exact ⟨t, by omega⟩

lemma one_not_mem_squareCore : 1 ∉ squareCore := by
  intro h
  rcases squareCore_even h with ⟨k, hk⟩
  omega

lemma one_mem_squareRange : 1 ∈ squareRange := by
  simpa using odd_mem_squareRange 0

lemma squareCore_ssubset_range : squareCore ⊂ squareRange := by
  refine ⟨squareCore_subset_range, ?_⟩
  intro h
  exact one_not_mem_squareCore (h one_mem_squareRange)

lemma squareCore_infinite : squareCore.Infinite := by
  let index : ℕ → ℕ := fun n => (n + 1) * (n + 1) + (n + 1)
  let f : ℕ → ℕ := fun n => 2 * index n
  have hindex : Function.Injective index := by
    intro a b hab
    dsimp [index] at hab
    nlinarith
  have hf : Function.Injective f := by
    intro a b h
    apply hindex
    dsimp [f] at h
    omega
  have hr : Set.range f ⊆ squareCore := by
    rintro x ⟨n, rfl⟩
    refine ⟨index n, ?_, rfl⟩
    intro hs
    rcases hs with ⟨k, hk⟩
    dsimp [index] at hk
    by_cases hkn : k ≤ n + 1
    · nlinarith
    · have hnk : n + 2 ≤ k := by omega
      nlinarith
  exact (Set.infinite_range_of_injective hf).mono hr

lemma squareRange_infinite : squareRange.Infinite :=
  squareCore_infinite.mono squareCore_subset_range

lemma squareRange_vanishingNoise :
    GenLimit.InfiniteContamination.VanishingNoise squareStream squareRange := by
  have hzero : ∀ n, GenLimit.InfiniteContamination.empiricalNoiseRate
      squareStream squareRange n = 0 := by
    intro n
    simp [GenLimit.InfiniteContamination.empiricalNoiseRate,
      GenLimit.InfiniteContamination.noiseCount, squareRange]
  unfold GenLimit.InfiniteContamination.VanishingNoise
  convert (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0)) using 1
  funext n
  exact hzero n

lemma squareRange_legal : Stage3Case024.Legal squareStream squareRange := by
  refine ⟨squareRange_infinite, squareStream_injective, Set.Subset.rfl, ?_⟩
  exact squareRange_vanishingNoise

lemma squareCore_legal_of_noise
    (hnoise : GenLimit.InfiniteContamination.VanishingNoise squareStream squareCore) :
    Stage3Case024.Legal squareStream squareCore := by
  exact ⟨squareCore_infinite, squareStream_injective, squareCore_subset_range, hnoise⟩

theorem checked_structural_witness :
    ∃ K₀ K₁ : Language, ∃ input : Stream,
      K₀ ⊂ K₁ ∧ K₀.Infinite ∧ K₁.Infinite ∧
      K₀ ⊆ Set.range input ∧ K₁ ⊆ Set.range input := by
  refine ⟨squareCore, squareRange, squareStream, squareCore_ssubset_range,
    squareCore_infinite, squareRange_infinite, squareCore_subset_range, ?_⟩
  exact Set.Subset.rfl

end Case024Formalization
