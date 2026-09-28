import «output».Pair
import Mathlib.Data.Nat.Pairing

namespace Case024

noncomputable def candidate (t k : ℕ) : ℕ := (Nat.pair t k)^2

lemma candidate_injective (t : ℕ) : Function.Injective (candidate t) := by
  intro a b hab
  have hp : Nat.pair t a = Nat.pair t b :=
    (Nat.pow_left_injective (by decide : 2 ≠ 0)) hab
  exact (Nat.pair_eq_pair.mp hp).2

lemma candidate_cross_injective {t s a b : ℕ} (h : candidate t a = candidate s b) : t = s := by
  have hp : Nat.pair t a = Nat.pair s b :=
    (Nat.pow_left_injective (by decide : 2 ≠ 0)) h
  exact (Nat.pair_eq_pair.mp hp).1

lemma candidate_mem_squares (t k : ℕ) : candidate t k ∈ squares := by
  exact ⟨Nat.pair t k, rfl⟩

lemma exists_fresh_index (t : ℕ) (xs : Fin (t + 1) → ℕ) :
    ∃ k, candidate t k ∉ Finset.univ.image xs := by
  classical
  have hinf : (Set.range (candidate t)).Infinite :=
    Set.infinite_range_of_injective (candidate_injective t)
  obtain ⟨z, ⟨k, rfl⟩, hz⟩ := hinf.exists_notMem_finset (Finset.univ.image xs)
  exact ⟨k, hz⟩

noncomputable def freshIndex (t : ℕ) (xs : Fin (t + 1) → ℕ) : ℕ :=
  Classical.choose (exists_fresh_index t xs)

lemma freshIndex_fresh (t : ℕ) (xs : Fin (t + 1) → ℕ) :
    candidate t (freshIndex t xs) ∉ Finset.univ.image xs :=
  Classical.choose_spec (exists_fresh_index t xs)

noncomputable def squareGenerator : Stage3Case024.OnlineGenerator := fun t xs _ =>
  candidate t (freshIndex t xs)

noncomputable def squareOutput (input : Stage3Case024.Stream) : Stage3Case024.Stream := fun t =>
  squareGenerator t (fun i => input i) (fun _ => 0)

lemma squareOutput_follows (input : Stage3Case024.Stream) :
    Stage3Case024.Follows squareGenerator input (squareOutput input) := by
  intro t
  rfl

lemma squareOutput_novel (input : Stage3Case024.Stream) :
    GenLimit.NovelGeneratesInLimit input (squareOutput input) squares := by
  refine ⟨0, fun t _ => ⟨candidate_mem_squares _ _, ?_, ?_⟩⟩
  · intro hmem
    unfold GenLimit.sample at hmem
    have hfresh := freshIndex_fresh t (fun i : Fin (t + 1) => input i)
    apply hfresh
    rcases Finset.mem_image.mp hmem with ⟨a, ha, hout⟩
    apply Finset.mem_image.2
    exact ⟨⟨a, by simpa using ha⟩, Finset.mem_univ _, by simpa [squareOutput, squareGenerator] using hout⟩
  · intro s hst heq
    exact (Nat.ne_of_lt hst) (candidate_cross_injective heq)

end Case024
