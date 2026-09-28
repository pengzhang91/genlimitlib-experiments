import Stage3Model

open Stage3Case025

namespace Case025Formalization

def inputSeen {t : ℕ} (input : Fin (t + 1) → ℕ) : Finset ℕ :=
  Finset.univ.image input

def outputSeen {t : ℕ} (output : Fin t → ℕ) : Finset ℕ :=
  Finset.univ.image output

noncomputable def freshGenerator : OnlineGenerator :=
  fun _ input output =>
    Nat.find (Set.Finite.exists_not_mem
      ((inputSeen input : Set ℕ) ∪ (outputSeen output : Set ℕ)).toFinite)

theorem freshGenerator_not_inputSeen
    (t : ℕ) (input : Fin (t + 1) → ℕ) (output : Fin t → ℕ) :
    freshGenerator t input output ∉ inputSeen input := by
  intro h
  have hnot := Nat.find_spec (Set.Finite.exists_not_mem
    ((inputSeen input : Set ℕ) ∪ (outputSeen output : Set ℕ)).toFinite)
  exact hnot (Set.mem_union_left _ h)

theorem freshGenerator_not_outputSeen
    (t : ℕ) (input : Fin (t + 1) → ℕ) (output : Fin t → ℕ) :
    freshGenerator t input output ∉ outputSeen output := by
  intro h
  have hnot := Nat.find_spec (Set.Finite.exists_not_mem
    ((inputSeen input : Set ℕ) ∪ (outputSeen output : Set ℕ)).toFinite)
  exact hnot (Set.mem_union_right _ h)

def trajectory (gen : OnlineGenerator) (input : Stream) : Stream
  | t => gen t (fun i => input i) (fun i => trajectory gen input i)

theorem trajectory_follows (gen : OnlineGenerator) (input : Stream) :
    Follows gen input (trajectory gen input) := by
  intro t
  exact trajectory.eq_1 gen input t

theorem fresh_trajectory_avoids_input (input : Stream) (t : ℕ) :
    trajectory freshGenerator input t ∉ GenLimit.sample input (t + 1) := by
  intro h
  have hmem : trajectory freshGenerator input t ∈
      inputSeen (fun i : Fin (t + 1) => input i) := by
    rw [inputSeen, Finset.mem_image]
    rw [GenLimit.sample, Finset.mem_image] at h
    obtain ⟨s, hs, heq⟩ := h
    exact ⟨⟨s, Finset.mem_range.mp hs⟩, Finset.mem_univ _, heq⟩
  apply freshGenerator_not_inputSeen t
    (fun i : Fin (t + 1) => input i)
    (fun i : Fin t => trajectory freshGenerator input i)
  rw [← trajectory.eq_1 freshGenerator input t]
  exact hmem

theorem fresh_trajectory_injective (input : Stream) :
    Function.Injective (trajectory freshGenerator input) := by
  intro a b hab
  rcases lt_trichotomy a b with hlt | rfl | hgt
  · have hmem : trajectory freshGenerator input a ∈
        outputSeen (fun i : Fin b => trajectory freshGenerator input i) := by
      rw [outputSeen, Finset.mem_image]
      exact ⟨⟨a, hlt⟩, Finset.mem_univ _, rfl⟩
    have hnot : trajectory freshGenerator input b ∉
        outputSeen (fun i : Fin b => trajectory freshGenerator input i) := by
      rw [trajectory.eq_1]
      exact freshGenerator_not_outputSeen b
        (fun i : Fin (b + 1) => input i)
        (fun i : Fin b => trajectory freshGenerator input i)
    exact (hnot (hab ▸ hmem)).elim
  · rfl
  · have hmem : trajectory freshGenerator input b ∈
        outputSeen (fun i : Fin a => trajectory freshGenerator input i) := by
      rw [outputSeen, Finset.mem_image]
      exact ⟨⟨b, hgt⟩, Finset.mem_univ _, rfl⟩
    have hnot : trajectory freshGenerator input a ∉
        outputSeen (fun i : Fin a => trajectory freshGenerator input i) := by
      rw [trajectory.eq_1]
      exact freshGenerator_not_outputSeen a
        (fun i : Fin (a + 1) => input i)
        (fun i : Fin a => trajectory freshGenerator input i)
    exact (hnot (hab.symm ▸ hmem)).elim

theorem fresh_trajectory_novel_except_validity (input : Stream) :
    (∀ t, trajectory freshGenerator input t ∉ GenLimit.sample input (t + 1)) ∧
    Function.Injective (trajectory freshGenerator input) := by
  exact ⟨fresh_trajectory_avoids_input input, fresh_trajectory_injective input⟩

theorem fresh_trajectory_novel_of_eventually_mem
    (input : Stream) (K : Language)
    (hvalid : ∃ T, ∀ t, T ≤ t → trajectory freshGenerator input t ∈ K) :
    GenLimit.NovelGeneratesInLimit input (trajectory freshGenerator input) K := by
  obtain ⟨T, hT⟩ := hvalid
  refine ⟨T, fun t ht => ⟨hT t ht, fresh_trajectory_avoids_input input t, ?_⟩⟩
  intro s hs heq
  exact (fresh_trajectory_injective input heq).not_lt hs

theorem fresh_trajectory_generatorFirst (input : Stream) :
    Set.range (trajectory freshGenerator input) ⊆
      GenLimit.GeneratorFirst input (trajectory freshGenerator input) := by
  rintro z ⟨t, rfl⟩
  refine ⟨t, rfl, ?_⟩
  intro s hs heq
  apply fresh_trajectory_avoids_input input t
  rw [GenLimit.sample]
  simp only [Finset.mem_image, Finset.mem_range]
  exact ⟨s, Nat.lt_succ_iff.mpr hs, heq⟩

end Case025Formalization
