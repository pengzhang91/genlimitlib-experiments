import Stage3Model
import Mathlib.Data.Nat.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.Bochner.L1

open Filter MeasureTheory Set
open scoped Topology

namespace Case024

abbrev Language := Stage3Case024.Language
abbrev Stream := Stage3Case024.Stream

noncomputable def squareTime (t : ℕ) : Prop := ∃ k : ℕ, t = k * k

noncomputable instance (t : ℕ) : Decidable (squareTime t) := Classical.propDecidable _

noncomputable def core : Language :=
  {x | ∃ t : ℕ, ¬ squareTime t ∧ x = 2 * (t + 1) * (t + 1)}

noncomputable def commonStream (t : ℕ) : ℕ :=
  if h : squareTime t then 2 * Nat.sqrt t + 1 else 2 * (t + 1) * (t + 1)

noncomputable def family (r : ℕ) (j : Fin r) : Language :=
  core ∪ {x | ∃ n : ℕ, x = 2 * n + 1 ∧ n % (r - 1) < (j : ℕ)}

lemma squareTime_sq (k : ℕ) : squareTime (k * k) := ⟨k, rfl⟩

lemma sqrt_sq (k : ℕ) : Nat.sqrt (k * k) = k := by simp

lemma commonStream_sq (k : ℕ) : commonStream (k * k) = 2 * k + 1 := by
  simp [commonStream, squareTime_sq]

lemma commonStream_nonsquare {t : ℕ} (h : ¬ squareTime t) :
    commonStream t = 2 * (t + 1) * (t + 1) := by simp [commonStream, h]

lemma core_even {x : ℕ} (hx : x ∈ core) : Even x := by
  rcases hx with ⟨t, ht, rfl⟩
  exact ⟨(t + 1) * (t + 1), by ring⟩

lemma odd_not_core (n : ℕ) : 2 * n + 1 ∉ core := by
  intro h
  obtain ⟨k, hk⟩ := core_even h
  omega

lemma commonStream_injective : Function.Injective commonStream := by
  intro a b hab
  by_cases ha : squareTime a
  · by_cases hb : squareTime b
    · rcases ha with ⟨i, rfl⟩
      rcases hb with ⟨j, rfl⟩
      simp only [commonStream_sq] at hab
      have : i = j := by omega
      subst j
      rfl
    · rw [commonStream_nonsquare hb] at hab
      rcases ha with ⟨i, rfl⟩
      rw [commonStream_sq] at hab
      have he : Even (2 * (b + 1) * (b + 1)) := ⟨(b + 1) * (b + 1), by ring⟩
      rw [← hab] at he
      exact (Nat.not_even_two_mul_add_one i he).elim
  · by_cases hb : squareTime b
    · rw [commonStream_nonsquare ha] at hab
      rcases hb with ⟨j, rfl⟩
      rw [commonStream_sq] at hab
      have he : Even (2 * (a + 1) * (a + 1)) := ⟨(a + 1) * (a + 1), by ring⟩
      rw [hab] at he
      exact (Nat.not_even_two_mul_add_one j he).elim
    · rw [commonStream_nonsquare ha, commonStream_nonsquare hb] at hab
      nlinarith

lemma core_subset_range : core ⊆ Set.range commonStream := by
  rintro x ⟨t, ht, rfl⟩
  exact ⟨t, commonStream_nonsquare ht⟩

lemma odd_subset_range : {x : ℕ | ∃ n : ℕ, x = 2 * n + 1} ⊆ Set.range commonStream := by
  rintro x ⟨n, rfl⟩
  exact ⟨n * n, commonStream_sq n⟩

lemma core_infinite : core.Infinite := by
  let f : ℕ → ℕ := fun n => 2 * (((n + 1) * (n + 1) + 1) + 1) * (((n + 1) * (n + 1) + 1) + 1)
  have hfmem : ∀ n, f n ∈ core := by
    intro n
    refine ⟨(n + 1) * (n + 1) + 1, ?_, rfl⟩
    rintro ⟨k, hk⟩
    have hlow : (n + 1) * (n + 1) < k * k := by omega
    have hkgt : n + 1 < k := (Nat.mul_self_lt_mul_self_iff).mp hlow
    have hupp : k * k < (n + 2) * (n + 2) := by nlinarith
    have hklt : k < n + 2 := (Nat.mul_self_lt_mul_self_iff).mp hupp
    omega
  apply (Set.infinite_range_of_injective (f := f) ?_).mono
  · rintro x ⟨n, rfl⟩
    exact hfmem n
  · intro a b hab
    dsimp [f] at hab
    simp only [mul_assoc] at hab
    have hsq : ((a + 1) * (a + 1) + 1 + 1) * ((a + 1) * (a + 1) + 1 + 1) =
        ((b + 1) * (b + 1) + 1 + 1) * ((b + 1) * (b + 1) + 1 + 1) :=
      Nat.mul_left_cancel (by omega) hab
    have hbase := Nat.mul_self_inj.mp hsq
    nlinarith

lemma family_infinite (r : ℕ) (j : Fin r) : (family r j).Infinite := by
  exact core_infinite.mono (by intro x hx; exact Or.inl hx)

lemma family_subset_range (r : ℕ) (j : Fin r) : family r j ⊆ Set.range commonStream := by
  intro x hx
  rcases hx with hx | ⟨n, rfl, hn⟩
  · exact core_subset_range hx
  · exact odd_subset_range ⟨n, rfl⟩

lemma family_strictlyNested {r : ℕ} (hr : 2 ≤ r) :
    Stage3Case024.StrictlyNested (family r) := by
  intro i j hij
  have hi : (i : ℕ) < r - 1 := by omega
  constructor
  · intro x hx
    rcases hx with hx | ⟨n, hxn, hn⟩
    · exact Or.inl hx
    · exact Or.inr ⟨n, hxn, hn.trans hij⟩
  · intro hsub
    let x := 2 * (i : ℕ) + 1
    have hxj : x ∈ family r j := by
      right
      refine ⟨i, rfl, ?_⟩
      simpa [Nat.mod_eq_of_lt hi] using hij
    have hxi : x ∉ family r i := by
      intro hx
      rcases hx with hx | ⟨n, hn, hlt⟩
      · exact odd_not_core i hx
      · have hni : n = i := by omega
        subst n
        simpa [Nat.mod_eq_of_lt hi] using hlt
    exact hxi (hsub hxj)


end Case024

open Case024

theorem stage3_result : Stage3Case024.MainClaim := by
  sorry
