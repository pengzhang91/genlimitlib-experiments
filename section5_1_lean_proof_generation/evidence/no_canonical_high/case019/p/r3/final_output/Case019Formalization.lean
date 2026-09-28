import Stage3Model
import Mathlib.Data.Set.Countable
import Mathlib.Data.Nat.Nth

open Stage3Case019

namespace Case019Formalization

/-- A simple extensional uncountable class of infinite integer languages.  This
is the structural core needed by the separation construction. -/
def encodedLanguage (A : Set ℕ) : Language ℤ :=
  {z | z < 0 ∨ ∃ n ∈ A, z = Int.ofNat n}

def encodedFamily : LanguageClass ℤ := Set.range encodedLanguage

lemma encodedLanguage_ofNat_iff (A : Set ℕ) (n : ℕ) :
    Int.ofNat n ∈ encodedLanguage A ↔ n ∈ A := by
  simp [encodedLanguage]

lemma encodedLanguage_injective : Function.Injective encodedLanguage := by
  intro A B h
  ext n
  rw [← encodedLanguage_ofNat_iff A n, ← encodedLanguage_ofNat_iff B n, h]

lemma powerset_nat_not_countable : ¬ Countable (Set ℕ) := by
  intro hcount
  letI : Countable (Set ℕ) := hcount
  obtain ⟨f : ℕ → Set ℕ, hf⟩ :=
    (countable_iff_exists_surjective (α := Set ℕ)).mp inferInstance
  let diagonal : Set ℕ := {n | n ∉ f n}
  obtain ⟨k, hk⟩ := hf diagonal
  have hiff : k ∈ diagonal ↔ k ∉ f k := by rfl
  rw [hk] at hiff
  by_cases hmem : k ∈ diagonal
  · exact (hiff.mp hmem) hmem
  · exact hmem (hiff.mpr hmem)

lemma encodedFamily_not_countable : ¬ encodedFamily.Countable := by
  intro hcount
  letI : Countable encodedFamily := hcount.to_subtype
  let lift : Set ℕ → encodedFamily := fun A => ⟨encodedLanguage A, ⟨A, rfl⟩⟩
  have hlift : Function.Injective lift := by
    intro A B h
    apply encodedLanguage_injective
    exact congrArg Subtype.val h
  exact powerset_nat_not_countable hlift.countable

lemma negativeRay_infinite :
    Set.Infinite {z : ℤ | z < 0} := by
  let f : ℕ → ℤ := Int.negSucc
  have hf : Function.Injective f := by
    intro m n h
    exact Int.negSucc_inj.mp h
  exact Set.infinite_of_injective_forall_mem hf (by
    intro n
    exact Int.negSucc_lt_zero n)

lemma encodedLanguage_infinite (A : Set ℕ) : (encodedLanguage A).Infinite := by
  apply negativeRay_infinite.mono
  intro z hz
  exact Or.inl hz

/-- Checked structural milestone for the uncountable separation clause. -/
theorem uncountable_infinite_integer_family :
    ∃ family : LanguageClass ℤ,
      ¬ family.Countable ∧ ∀ K ∈ family, K.Infinite := by
  refine ⟨encodedFamily, encodedFamily_not_countable, ?_⟩
  rintro K ⟨A, rfl⟩
  exact encodedLanguage_infinite A

end Case019Formalization

namespace Case019Formalization

noncomputable def negativeNthGenerator : Generator ℤ :=
  fun t xs =>
    Int.negSucc (Nat.nth (fun n => ∀ i, xs i ≠ Int.negSucc n) t)

lemma negativeMissing_infinite {t : ℕ} (xs : Fin t → ℤ) :
    Set.Infinite {n : ℕ | ∀ i, xs i ≠ Int.negSucc n} := by
  have hbad : Set.Finite {n : ℕ | ∃ i, xs i = Int.negSucc n} := by
    change Set.Finite (Int.negSucc ⁻¹' Set.range xs)
    have hinj : Function.Injective Int.negSucc := fun _ _ h => Int.negSucc_inj.mp h
    exact (Set.finite_range xs).preimage hinj.injOn
  have hcomp := hbad.infinite_compl
  convert hcomp using 1
  ext n
  simp [eq_comm]

lemma negativeNthGenerator_negative {t : ℕ} (xs : Fin t → ℤ) :
    negativeNthGenerator t xs < 0 := by
  exact Int.negSucc_lt_zero _

lemma negativeNthGenerator_avoids_history {t : ℕ} (xs : Fin t → ℤ) (i : Fin t) :
    negativeNthGenerator t xs ≠ xs i := by
  have hmem := Nat.nth_mem_of_infinite (negativeMissing_infinite xs) t
  exact (hmem i).symm

lemma negativeNthGenerator_all_round_sample_fresh
    (input : Stream ℤ) (t : ℕ) :
    outputAfterInput negativeNthGenerator input t ∉
      GenLimit.Generic.sample input (t + 1) := by
  intro hmem
  rw [GenLimit.Generic.sample] at hmem
  simp only [Finset.mem_image, Finset.mem_range] at hmem
  obtain ⟨i, hi, heq⟩ := hmem
  have havoid := negativeNthGenerator_avoids_history
    (fun j : Fin (t + 1) => input j) ⟨i, hi⟩
  exact havoid heq.symm

lemma negativeNthGenerator_in_encodedLanguage
    (A : Set ℕ) (input : Stream ℤ) (t : ℕ) :
    outputAfterInput negativeNthGenerator input t ∈ encodedLanguage A := by
  change negativeNthGenerator (t + 1) (fun j : Fin (t + 1) => input j) ∈ encodedLanguage A
  exact Or.inl (negativeNthGenerator_negative _)

/-- A single semantic generator is target-valid and same-round sample-fresh
on every language in the uncountable class, independently of the noise level.
The missing obligations for the requested positive separation are output
non-repetition and the quarter-density estimate. -/
theorem uncountable_family_all_round_sample_fresh :
    ∃ family : LanguageClass ℤ, ¬ family.Countable ∧
      ∃ gen : Generator ℤ,
        ∀ K ∈ family, ∀ input : Stream ℤ, ∀ t,
          outputAfterInput gen input t ∈ K ∧
            outputAfterInput gen input t ∉
              GenLimit.Generic.sample input (t + 1) := by
  refine ⟨encodedFamily, encodedFamily_not_countable, negativeNthGenerator, ?_⟩
  rintro K ⟨A, rfl⟩ input t
  exact ⟨negativeNthGenerator_in_encodedLanguage A input t,
    negativeNthGenerator_all_round_sample_fresh input t⟩

end Case019Formalization

namespace Case019Formalization

lemma nth_le_nth_of_imp {p r : ℕ → Prop}
    (hp : Set.Infinite {n | p n}) (hr : Set.Infinite {n | r n})
    (himp : ∀ n, r n → p n) (k : ℕ) :
    Nat.nth p k ≤ Nat.nth r k := by
  classical
  have hcount : Nat.count r (Nat.nth r k + 1) ≤
      Nat.count p (Nat.nth r k + 1) := by
    rw [Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range]
    apply Finset.card_le_card
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_range] at hn ⊢
    exact ⟨hn.1, himp n hn.2⟩
  rw [Nat.count_nth_succ_of_infinite hr] at hcount
  exact Nat.le_of_lt_succ (Nat.nth_lt_of_lt_count
    (lt_of_lt_of_le (Nat.lt_succ_self k) hcount))

def missingAt (input : Stream ℤ) (t n : ℕ) : Prop :=
  ∀ i : Fin (t + 1), input i ≠ Int.negSucc n

lemma missingAt_infinite (input : Stream ℤ) (t : ℕ) :
    Set.Infinite {n | missingAt input t n} :=
  negativeMissing_infinite (fun i : Fin (t + 1) => input i)

lemma missingAt_anti (input : Stream ℤ) {s t n : ℕ} (hst : s < t) :
    missingAt input t n → missingAt input s n := by
  intro h i
  apply h ⟨i, lt_of_lt_of_le i.isLt (Nat.succ_le_succ hst.le)⟩

lemma negativeNthGenerator_outputs_ne (input : Stream ℤ) {s t : ℕ} (hst : s < t) :
    outputAfterInput negativeNthGenerator input s ≠
      outputAfterInput negativeNthGenerator input t := by
  have hlt : Nat.nth (missingAt input s) (s + 1) <
      Nat.nth (missingAt input t) (t + 1) := by
    calc
      Nat.nth (missingAt input s) (s + 1) <
          Nat.nth (missingAt input s) (t + 1) :=
        (Nat.nth_lt_nth (missingAt_infinite input s)).2
          (Nat.succ_lt_succ hst)
      _ ≤ Nat.nth (missingAt input t) (t + 1) :=
        nth_le_nth_of_imp (missingAt_infinite input s)
          (missingAt_infinite input t) (fun n => missingAt_anti input hst) _
  intro heq
  have hind : Nat.nth (missingAt input s) (s + 1) =
      Nat.nth (missingAt input t) (t + 1) := by
    exact Int.negSucc_inj.mp heq
  exact hlt.ne hind

lemma negativeNthGenerator_novel
    (A : Set ℕ) (input : Stream ℤ) :
    NovelGeneratesAfterInput input
      (outputAfterInput negativeNthGenerator input) (encodedLanguage A) := by
  refine ⟨0, fun t _ => ⟨negativeNthGenerator_in_encodedLanguage A input t,
    negativeNthGenerator_all_round_sample_fresh input t, ?_⟩⟩
  intro s hst
  exact negativeNthGenerator_outputs_ne input hst

/-- The positive generation-in-the-limit part of the separation construction
is checked for an uncountable family, at every contamination level. -/
theorem uncountable_family_novel_at_every_level :
    ∀ q, ∃ family : LanguageClass ℤ,
      ¬ family.Countable ∧ (∀ K ∈ family, K.Infinite) ∧
      ∃ gen : Generator ℤ,
        ∀ K ∈ family, ∀ input : Stream ℤ,
          GenLimit.Generic.InjectiveValueContaminatedPresentationAtMost input K q →
            NovelGeneratesAfterInput input (outputAfterInput gen input) K := by
  intro q
  refine ⟨encodedFamily, encodedFamily_not_countable, ?_, negativeNthGenerator, ?_⟩
  · rintro K ⟨A, rfl⟩
    exact encodedLanguage_infinite A
  · rintro K ⟨A, rfl⟩ input _
    exact negativeNthGenerator_novel A input

end Case019Formalization
