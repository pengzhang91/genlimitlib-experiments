import Stage3Model
import Mathlib.Logic.Equiv.Finset

open Set
open Stage3Case025

namespace Case025

noncomputable def decodedFinset (n : ℕ) : Finset ℕ :=
  (Encodable.decode n : Option (Finset ℕ)).getD ∅

noncomputable def finiteExtensionFamily
    (family : ℕ → Language) (n : ℕ) : Language :=
  family (Nat.unpair n).1 ∪ (decodedFinset (Nat.unpair n).2 : Set ℕ)

lemma decodedFinset_encode (F : Finset ℕ) :
    decodedFinset (Encodable.encode F) = F := by
  simp [decodedFinset, Encodable.encodek]

lemma finiteExtensionFamily_infinite
    (family : ℕ → Language) (hfamily : ∀ i, (family i).Infinite) :
    ∀ n, (finiteExtensionFamily family n).Infinite := by
  intro n
  exact (hfamily (Nat.unpair n).1).mono subset_union_left

lemma finiteExtensionFamily_covers
    (family : ℕ → Language) (i : ℕ) (F : Finset ℕ) :
    finiteExtensionFamily family (Nat.pair i (Encodable.encode F)) =
      family i ∪ (F : Set ℕ) := by
  simp [finiteExtensionFamily, decodedFinset_encode]

noncomputable def badValues (input : Stream) (K : Language) : Set ℕ :=
  input '' GenLimit.Generic.ViolationIndices input (fun x => x ∈ K)

lemma badValues_finite {input : Stream} {K : Language}
    (hbad : GenLimit.Generic.FinitelyManyViolations input (fun x => x ∈ K)) :
    (badValues input K).Finite := by
  exact hbad.image input

lemma range_eq_union_badValues {input : Stream} {K : Language}
    (hcover : K ⊆ Set.range input) :
    Set.range input = K ∪ badValues input K := by
  ext x
  constructor
  · rintro ⟨t, rfl⟩
    by_cases hx : input t ∈ K
    · exact Or.inl hx
    · exact Or.inr ⟨t, hx, rfl⟩
  · rintro (hx | hx)
    · exact hcover hx
    · rcases hx with ⟨t, -, rfl⟩
      exact ⟨t, rfl⟩

lemma range_finite_extension {input : Stream} {K : Language}
    (hp : CompleteFiniteOccurrencePresentation input K) :
    ∃ F : Finset ℕ, Set.range input = K ∪ (F : Set ℕ) := by
  rcases hp with ⟨hcover, hbad⟩
  let F := (badValues_finite hbad).toFinset
  refine ⟨F, ?_⟩
  rw [range_eq_union_badValues hcover]
  simp [F]

lemma presents_some_finiteExtension
    (family : ℕ → Language) {i : ℕ} {input : Stream}
    (hp : CompleteFiniteOccurrencePresentation input (family i)) :
    ∃ j, GenLimit.Presents input (finiteExtensionFamily family j) := by
  rcases range_finite_extension hp with ⟨F, hF⟩
  refine ⟨Nat.pair i (Encodable.encode F), ?_⟩
  rw [GenLimit.Presents, finiteExtensionFamily_covers]
  exact hF

lemma eventual_mem_of_novel_of_finite_diff
    {input output : Stream} {R K : Language}
    (hnovel : GenLimit.NovelGeneratesInLimit input output R)
    (hfinite : (R \ K).Finite) :
    ∃ T, ∀ t, T ≤ t → output t ∈ K := by
  rcases hnovel with ⟨T, hT⟩
  let badTimes : Set ℕ := {t | T ≤ t ∧ output t ∈ R \ K}
  have himage : (output '' badTimes).Finite := by
    apply hfinite.subset
    rintro x ⟨t, ht, rfl⟩
    exact ht.2
  have hinj : Set.InjOn output badTimes := by
    intro a ha b hb hab
    rcases lt_trichotomy a b with hablt | rfl | hbalt
    · exact False.elim ((hT b hb.1).2.2 a hablt hab)
    · rfl
    · exact False.elim ((hT a ha.1).2.2 b hbalt hab.symm)
  have hbadTimes : badTimes.Finite := himage.of_finite_image hinj
  rcases hbadTimes.bddAbove with ⟨B, hB⟩
  refine ⟨max T (B + 1), fun t ht => ?_⟩
  have hTt : T ≤ t := le_trans (le_max_left _ _) ht
  have houtR := (hT t hTt).1
  by_contra houtK
  have htbad : t ∈ badTimes := ⟨hTt, houtR, houtK⟩
  have htB : t ≤ B := hB htbad
  omega

end Case025

namespace Case025

lemma novel_of_novel_of_finite_diff
    {input output : Stream} {R K : Language}
    (hnovel : GenLimit.NovelGeneratesInLimit input output R)
    (hfinite : (R \ K).Finite) :
    GenLimit.NovelGeneratesInLimit input output K := by
  rcases hnovel with ⟨T₁, hT₁⟩
  rcases eventual_mem_of_novel_of_finite_diff
      (input := input) (output := output) (R := R) (K := K)
      ⟨T₁, hT₁⟩ hfinite with ⟨T₂, hT₂⟩
  refine ⟨max T₁ T₂, fun t ht => ?_⟩
  have ht₁ : T₁ ≤ t := le_trans (le_max_left _ _) ht
  have ht₂ : T₂ ≤ t := le_trans (le_max_right _ _) ht
  exact ⟨hT₂ t ht₂, (hT₁ t ht₁).2⟩

lemma range_diff_target_finite
    {input : Stream} {K : Language}
    (hp : CompleteFiniteOccurrencePresentation input K) :
    (Set.range input \ K).Finite := by
  rcases range_finite_extension hp with ⟨F, hF⟩
  rw [hF]
  exact Set.Finite.subset (F.finite_toSet) (by
    intro x hx
    exact hx.1.resolve_left hx.2)

end Case025
