import Stage3Model
import Mathlib.Logic.Equiv.Finset
import Mathlib.Data.Nat.Pairing

open Set

namespace Stage3Case025

noncomputable def decodedFinset (n : ℕ) : Finset ℕ :=
  (Encodable.decode n : Option (Finset ℕ)).getD ∅

def finiteExpansion (family : ℕ → Language) (n : ℕ) : Language :=
  family (Nat.unpair n).1 ∪ (decodedFinset (Nat.unpair n).2 : Set ℕ)

lemma decodedFinset_encode (F : Finset ℕ) :
    decodedFinset (Encodable.encode F) = F := by
  simp [decodedFinset]

lemma finiteExpansion_contains (family : ℕ → Language) (i : ℕ) (F : Finset ℕ) :
    finiteExpansion family (Nat.pair i (Encodable.encode F)) =
      family i ∪ (F : Set ℕ) := by
  simp [finiteExpansion, decodedFinset]

lemma finiteExpansion_infinite
    (family : ℕ → Language) (hinf : ∀ i, (family i).Infinite) :
    ∀ n, (finiteExpansion family n).Infinite := by
  intro n
  exact (hinf (Nat.unpair n).1).mono (subset_union_left)

lemma range_diff_finite_of_finitelyManyViolations
    (input : Stream) (K : Language)
    (hbad : GenLimit.Generic.FinitelyManyViolations input (fun x => x ∈ K)) :
    (Set.range input \ K).Finite := by
  apply Set.Finite.subset (hbad.image input)
  rintro x ⟨⟨t, rfl⟩, hnot⟩
  exact ⟨t, hnot, rfl⟩

lemma range_eq_union_diff
    (input : Stream) (K : Language) (hcover : K ⊆ Set.range input) :
    Set.range input = K ∪ (Set.range input \ K) := by
  ext x
  by_cases hx : x ∈ K
  · simp [hx, hcover hx]
  · simp [hx]

lemma noisy_range_is_expansion
    (family : ℕ → Language) (i : ℕ) (input : Stream)
    (hp : CompleteFiniteOccurrencePresentation input (family i)) :
    ∃ n, GenLimit.Presents input (finiteExpansion family n) := by
  rcases hp with ⟨hcover, hbad⟩
  have hfin : (Set.range input \ family i).Finite :=
    range_diff_finite_of_finitelyManyViolations input (family i) hbad
  let F : Finset ℕ := hfin.toFinset
  refine ⟨Nat.pair i (Encodable.encode F), ?_⟩
  rw [GenLimit.Presents, finiteExpansion_contains]
  rw [range_eq_union_diff input (family i) hcover]
  congr 1
  ext x
  simp [F]

end Stage3Case025

namespace Stage3Case025

lemma novelGeneratesInLimit_of_subset_finite_diff
    (input output : Stream) (K R : Language)
    (hKR : K ⊆ R) (hfin : (R \ K).Finite)
    (hnovel : GenLimit.NovelGeneratesInLimit input output R) :
    GenLimit.NovelGeneratesInLimit input output K := by
  rcases hnovel with ⟨T, hT⟩
  let badTimes : Set ℕ := {t | T ≤ t ∧ output t ∈ R \ K}
  have himage : (output '' badTimes).Finite := by
    apply hfin.subset
    rintro x ⟨t, ht, rfl⟩
    exact ht.2
  have hinj : Set.InjOn output badTimes := by
    intro s hs t ht heq
    rcases lt_trichotomy s t with hlt | heqst | hgt
    · exact False.elim ((hT t ht.1).2.2 s hlt heq)
    · exact heqst
    · exact False.elim ((hT s hs.1).2.2 t hgt heq.symm)
  have hbad : badTimes.Finite := Set.Finite.of_finite_image himage hinj
  obtain ⟨B, hB⟩ := hbad.bddAbove
  refine ⟨max T (B + 1), ?_⟩
  intro t ht
  have htT : T ≤ t := le_trans (le_max_left _ _) ht
  have hbase := hT t htT
  refine ⟨?_, hbase.2.1, hbase.2.2⟩
  by_contra htK
  have htbad : t ∈ badTimes := ⟨htT, hbase.1, htK⟩
  have htB : t ≤ B := hB htbad
  have hBt : B + 1 ≤ t := le_trans (le_max_right _ _) ht
  omega

end Stage3Case025
