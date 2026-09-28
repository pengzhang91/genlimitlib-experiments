import Stage3Model
import Mathlib

open Set Function Filter
open scoped Topology

namespace Case019Work

open Stage3Case019

/-- The finite marker block distinguishing the two halves of the separation family. -/
def markers (q : ℕ) : Set ℤ := {z | ∃ n ≤ q, z = Int.ofNat n}

def positiveTail (j : ℕ) : Set ℤ := {z | Int.ofNat j < z}

def negativeHalf : Set ℤ := {z | z < 0}

/-- The adjacent-noise family from the supplied separation construction. -/
def separationFamily (q : ℕ) : LanguageClass ℤ :=
  {K | (markers q ⊆ K ∧ ∃ j, positiveTail j ⊆ K) ∨
       (negativeHalf ⊆ K ∧ Disjoint K (markers q))}

lemma markers_finite (q : ℕ) : (markers q).Finite := by
  refine Set.Finite.subset (Set.finite_range fun n : Fin (q + 1) => Int.ofNat n) ?_
  intro z hz
  rcases hz with ⟨n, hn, rfl⟩
  exact ⟨⟨n, by omega⟩, rfl⟩

lemma negativeHalf_infinite : negativeHalf.Infinite := by
  have hinj : Function.Injective (fun n : ℕ => -(Int.ofNat (n + 1))) := by
    intro a b hab
    simp at hab
    omega
  have hsub : Set.range (fun n : ℕ => -(Int.ofNat (n + 1))) ⊆ negativeHalf := by
    rintro z ⟨n, rfl⟩
    change -(Int.ofNat (n + 1)) < 0
    have hp : 0 < Int.ofNat (n + 1) := Int.ofNat_pos.mpr (by omega)
    omega
  exact (Set.infinite_range_of_injective hinj).mono hsub

lemma positiveTail_infinite (j : ℕ) : (positiveTail j).Infinite := by
  have hinj : Function.Injective (fun n : ℕ => Int.ofNat (j + n + 1)) := by
    intro a b hab
    simp at hab
    omega
  have hsub : Set.range (fun n : ℕ => Int.ofNat (j + n + 1)) ⊆ positiveTail j := by
    rintro z ⟨n, rfl⟩
    change Int.ofNat j < Int.ofNat (j + n + 1)
    exact Int.ofNat_lt.mpr (by omega)
  exact (Set.infinite_range_of_injective hinj).mono hsub

lemma separationFamily_languages_infinite (q : ℕ) :
    ∀ K ∈ separationFamily q, K.Infinite := by
  intro K hK
  rcases hK with hK | hK
  · rcases hK.2 with ⟨j, hj⟩
    exact (positiveTail_infinite j).mono hj
  · exact negativeHalf_infinite.mono hK.1

/-- Positive and negative rays used by the explicit semantic generator. -/
def sideValue (positive : Bool) (n : ℕ) : ℤ :=
  if positive then Int.ofNat (n + 1) else -Int.ofNat (n + 1)

lemma sideValue_injective (positive : Bool) : Function.Injective (sideValue positive) := by
  intro a b hab
  cases positive <;> simp [sideValue] at hab ⊢ <;> omega

lemma sideValue_range_infinite (positive : Bool) :
    (Set.range (sideValue positive)).Infinite := by
  exact Set.infinite_range_of_injective (sideValue_injective positive)

noncomputable def chooseFresh (positive : Bool) (banned : Finset ℤ) : ℤ :=
  Classical.choose ((sideValue_range_infinite positive).exists_notMem_finset banned)

lemma chooseFresh_spec (positive : Bool) (banned : Finset ℤ) :
    chooseFresh positive banned ∈ Set.range (sideValue positive) ∧
      chooseFresh positive banned ∉ banned := by
  exact Classical.choose_spec ((sideValue_range_infinite positive).exists_notMem_finset banned)

noncomputable def replayStep (q : ℕ)
    (state : List ℤ × List ℤ) (x : ℤ) : List ℤ × List ℤ := by
  classical
  let inputs := state.1 ++ [x]
  let positive : Bool := decide (markers q ⊆ (inputs.toFinset : Set ℤ))
  let y := chooseFresh positive (inputs.toFinset ∪ state.2.toFinset)
  exact (inputs, state.2 ++ [y])

noncomputable def replay (q : ℕ) (history : List ℤ) : List ℤ × List ℤ :=
  history.foldl (replayStep q) ([], [])

noncomputable def separationGenerator (q : ℕ) : Generator ℤ :=
  fun _ history => ((replay q (List.ofFn history)).2.getLast?).getD 0


/-- An injective powerset-sized subfamily of the negative half of the construction. -/
def encodedNegative (q : ℕ) (A : Set ℕ) : Set ℤ :=
  negativeHalf ∪ {z | ∃ n ∈ A, z = Int.ofNat (q + n + 1)}

lemma encodedNegative_mem (q : ℕ) (A : Set ℕ) :
    encodedNegative q A ∈ separationFamily q := by
  right
  constructor
  · exact Set.subset_union_left
  · rw [Set.disjoint_left]
    intro z hzK hzM
    rcases hzK with hzneg | hzenc
    · rcases hzM with ⟨n, hn, rfl⟩
      exact (Int.ofNat_nonneg n).not_lt hzneg
    · rcases hzenc with ⟨n, hnA, rfl⟩
      rcases hzM with ⟨m, hmq, hm⟩
      have hmnat : q + n + 1 = m := Int.ofNat_inj.mp hm
      omega

lemma encodedNegative_injective (q : ℕ) :
    Function.Injective (encodedNegative q) := by
  intro A B hAB
  ext n
  have hpos : ¬ Int.ofNat (q + n + 1) ∈ negativeHalf := by
    exact (Int.ofNat_nonneg (q + n + 1)).not_lt
  have hA : Int.ofNat (q + n + 1) ∈ encodedNegative q A ↔ n ∈ A := by
    constructor
    · intro h
      rcases h with h | h
      · exact (hpos h).elim
      · rcases h with ⟨m, hmA, hm⟩
        have hmnat : q + n + 1 = q + m + 1 := Int.ofNat_inj.mp hm
        have : m = n := by omega
        simpa [this] using hmA
    · intro hn
      exact Or.inr ⟨n, hn, rfl⟩
  have hB : Int.ofNat (q + n + 1) ∈ encodedNegative q B ↔ n ∈ B := by
    constructor
    · intro h
      rcases h with h | h
      · exact (hpos h).elim
      · rcases h with ⟨m, hmB, hm⟩
        have hmnat : q + n + 1 = q + m + 1 := Int.ofNat_inj.mp hm
        have : m = n := by omega
        simpa [this] using hmB
    · intro hn
      exact Or.inr ⟨n, hn, rfl⟩
  rw [← hA, hAB, hB]

lemma separationFamily_uncountable (q : ℕ) :
    ¬(separationFamily q).Countable := by
  intro hcount
  have hpre := hcount.preimage (encodedNegative_injective q)
  have huniv : (Set.univ : Set (Set ℕ)).Countable := by
    apply hpre.mono
    intro A _
    exact encodedNegative_mem q A
  rcases huniv.exists_surjective Set.univ_nonempty with ⟨f, hf⟩
  let D : Set ℕ := {n | n ∉ (f n : Set ℕ)}
  obtain ⟨k, hk⟩ := hf ⟨D, Set.mem_univ D⟩
  have heq : (f k : Set ℕ) = D := congrArg Subtype.val hk
  by_cases hmem : k ∈ D
  · have hnot : k ∉ (f k : Set ℕ) := by simpa [D] using hmem
    exact hnot (heq.symm ▸ hmem)
  · have hyes : k ∈ (f k : Set ℕ) := by
      by_contra hnot
      apply hmem
      simpa [D] using hnot
    exact hmem (heq ▸ hyes)

/-- Checked structural portion of the separation clause. -/
theorem separation_family_structural (q : ℕ) :
    ¬(separationFamily q).Countable ∧
      ∀ K ∈ separationFamily q, K.Infinite := by
  exact ⟨separationFamily_uncountable q, separationFamily_languages_infinite q⟩

end Case019Work
